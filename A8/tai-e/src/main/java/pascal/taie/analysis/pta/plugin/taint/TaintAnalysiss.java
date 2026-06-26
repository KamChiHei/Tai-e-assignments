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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    private final Map<Pointer, Set<TaintTransferEdge>> transferEdges = new LinkedHashMap<>();

    public void onNewCall(CSCallSite csCallSite, CSMethod csCallee) {
        Invoke callSite = csCallSite.getCallSite();
        JMethod callee = csCallee.getMethod();
        Context callerContext = csCallSite.getContext();
        processSource(callSite, callee, callerContext);
        processTransfers(callSite, callee, callerContext);
    }

    private void processSource(Invoke callSite, JMethod callee,
                               Context callerContext) {
        if (callSite.getResult() == null) {
            return;
        }
        for (Source source : config.getSources()) {
            if (source.method().equals(callee)) {
                CSObj taint = makeTaint(callSite, source.type());
                CSVar result = csManager.getCSVar(callerContext, callSite.getResult());
                solver.addVarPointsTo(result, PointsToSetFactory.make(taint));
            }
        }
    }

    private void processTransfers(Invoke callSite, JMethod callee,
                                  Context callerContext) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (!transfer.method().equals(callee)) {
                continue;
            }
            Var fromVar = getVar(callSite, transfer.from());
            Var toVar = getVar(callSite, transfer.to());
            if (fromVar == null || toVar == null) {
                continue;
            }
            CSVar from = csManager.getCSVar(callerContext, fromVar);
            CSVar to = csManager.getCSVar(callerContext, toVar);
            TaintTransferEdge edge = new TaintTransferEdge(to, transfer.type());
            if (transferEdges.computeIfAbsent(from, ignored -> new HashSet<>()).add(edge)) {
                transferTaints(from.getPointsToSet(), edge);
            }
        }
    }

    public void onNewPointsTo(Pointer pointer, PointsToSet delta) {
        Set<TaintTransferEdge> edges = transferEdges.get(pointer);
        if (edges != null) {
            edges.forEach(edge -> transferTaints(delta, edge));
        }
    }

    private void transferTaints(PointsToSet pointsToSet, TaintTransferEdge edge) {
        PointsToSet taints = PointsToSetFactory.make();
        for (CSObj csObj : pointsToSet) {
            if (manager.isTaint(csObj.getObject())) {
                Invoke sourceCall = manager.getSourceCall(csObj.getObject());
                taints.addObject(makeTaint(sourceCall, edge.type()));
            }
        }
        if (!taints.isEmpty()) {
            solver.addVarPointsTo(edge.to(), taints);
        }
    }

    private CSObj makeTaint(Invoke sourceCall, Type type) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(sourceCall, type));
    }

    private Var getVar(Invoke callSite, int index) {
        if (index == TaintTransfer.BASE) {
            if (callSite.getInvokeExp() instanceof InvokeInstanceExp invokeInstanceExp) {
                return invokeInstanceExp.getBase();
            }
            return null;
        }
        if (index == TaintTransfer.RESULT) {
            return callSite.getResult();
        }
        InvokeExp invokeExp = callSite.getInvokeExp();
        return index < invokeExp.getArgCount() ? invokeExp.getArg(index) : null;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        result.getCSCallGraph().edges().forEach(edge -> {
            CSCallSite csCallSite = edge.getCallSite();
            Invoke callSite = csCallSite.getCallSite();
            JMethod callee = edge.getCallee().getMethod();
            Context callerContext = csCallSite.getContext();
            for (Sink sink : config.getSinks()) {
                if (sink.method().equals(callee)) {
                    Var var = getVar(callSite, sink.index());
                    if (var != null) {
                        CSVar csVar = csManager.getCSVar(callerContext, var);
                        for (CSObj csObj : csVar.getPointsToSet()) {
                            if (manager.isTaint(csObj.getObject())) {
                                taintFlows.add(new TaintFlow(
                                        manager.getSourceCall(csObj.getObject()),
                                        callSite, sink.index()));
                            }
                        }
                    }
                }
            }
        });
        return taintFlows;
    }

    private record TaintTransferEdge(CSVar to, Type type) {
    }
}
