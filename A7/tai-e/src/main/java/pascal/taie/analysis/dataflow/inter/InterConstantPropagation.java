/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    private final List<StoreField> storeFields = new ArrayList<>();

    private final List<StoreArray> storeArrays = new ArrayList<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        storeFields.clear();
        storeArrays.clear();
        for (Stmt stmt : icfg) {
            if (stmt instanceof StoreField storeField) {
                storeFields.add(storeField);
            } else if (stmt instanceof StoreArray storeArray) {
                storeArrays.add(storeArray);
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (out.equals(in)) {
            return false;
        }
        out.clear();
        in.forEach(out::update);
        return true;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        out.clear();
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?, ?> defStmt &&
                defStmt.getLValue() instanceof Var lVar &&
                ConstantPropagation.canHoldInt(lVar)) {
            if (stmt instanceof LoadField loadField) {
                out.update(lVar, evaluateLoadField(loadField));
            } else if (stmt instanceof LoadArray loadArray) {
                out.update(lVar, evaluateLoadArray(loadArray, in));
            } else {
                out.update(lVar, ConstantPropagation.evaluate(
                        (Exp) defStmt.getRValue(), in));
            }
        }
        boolean changed = !out.equals(oldOut);
        if (changed && (stmt instanceof StoreField || stmt instanceof StoreArray)) {
            solver.addAllNodes();
        }
        return changed;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact result = out.copy();
        Stmt callSite = edge.getSource();
        if (callSite instanceof Invoke invoke) {
            Var lhs = invoke.getResult();
            if (lhs != null) {
                result.remove(lhs);
            }
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact result = new CPFact();
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        IR calleeIR = edge.getCallee().getIR();
        int limit = Math.min(invokeExp.getArgCount(), calleeIR.getParams().size());
        for (int i = 0; i < limit; ++i) {
            Var param = calleeIR.getParam(i);
            if (ConstantPropagation.canHoldInt(param)) {
                result.update(param, callSiteOut.get(invokeExp.getArg(i)));
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact result = new CPFact();
        Stmt callSite = edge.getCallSite();
        if (callSite instanceof Invoke invoke && invoke.getResult() != null) {
            Value ret = Value.getUndef();
            for (Var retVar : edge.getReturnVars()) {
                ret = cp.meetValue(ret, returnOut.get(retVar));
            }
            result.update(invoke.getResult(), ret);
        }
        return result;
    }

    private Value evaluateLoadField(LoadField load) {
        Value result = Value.getUndef();
        for (StoreField store : storeFields) {
            if (mayAlias(load, store)) {
                result = cp.meetValue(result,
                        solver.getInFact(store).get(store.getRValue()));
            }
        }
        return result;
    }

    private boolean mayAlias(LoadField load, StoreField store) {
        JField field = load.getFieldRef().resolve();
        if (!field.equals(store.getFieldRef().resolve())) {
            return false;
        }
        if (load.isStatic() || store.isStatic()) {
            return load.isStatic() && store.isStatic();
        }
        Var loadBase = ((InstanceFieldAccess) load.getFieldAccess()).getBase();
        Var storeBase = ((InstanceFieldAccess) store.getFieldAccess()).getBase();
        return hasIntersection(pta.getPointsToSet(loadBase),
                pta.getPointsToSet(storeBase));
    }

    private Value evaluateLoadArray(LoadArray load, CPFact in) {
        Value result = Value.getUndef();
        ArrayAccess loadAccess = load.getArrayAccess();
        Value loadIndex = in.get(loadAccess.getIndex());
        for (StoreArray store : storeArrays) {
            ArrayAccess storeAccess = store.getArrayAccess();
            if (hasIntersection(pta.getPointsToSet(loadAccess.getBase()),
                    pta.getPointsToSet(storeAccess.getBase()))) {
                CPFact storeIn = solver.getInFact(store);
                Value storeIndex = storeIn.get(storeAccess.getIndex());
                if (mayAliasIndex(loadIndex, storeIndex)) {
                    result = cp.meetValue(result, storeIn.get(store.getRValue()));
                }
            }
        }
        return result;
    }

    private static boolean mayAliasIndex(Value i, Value j) {
        if (i.isUndef() || j.isUndef()) {
            return false;
        }
        if (i.isNAC() || j.isNAC()) {
            return true;
        }
        return i.getConstant() == j.getConstant();
    }

    private static boolean hasIntersection(Set<Obj> s1, Set<Obj> s2) {
        if (s1.size() > s2.size()) {
            Set<Obj> tmp = s1;
            s1 = s2;
            s2 = tmp;
        }
        for (Obj obj : s1) {
            if (s2.contains(obj)) {
                return true;
            }
        }
        return false;
    }
}
