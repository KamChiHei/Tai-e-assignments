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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.addReachableMethod(method)) {
            return;
        }
        if (method.isAbstract()) {
            return;
        }
        method.getIR().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(field));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getStaticField(field),
                        pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            JMethod callee = resolveCallee(null, stmt);
            Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(stmt), stmt, callee);
            if (!callGraph.addEdge(edge)) {
                return null;
            }
            addReachable(callee);
            InvokeExp invokeExp = stmt.getInvokeExp();
            for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                addPFGEdge(pointerFlowGraph.getVarPtr(invokeExp.getArg(i)),
                        pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)));
            }
            if (stmt.getResult() != null) {
                for (Var ret : callee.getIR().getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                            pointerFlowGraph.getVarPtr(stmt.getResult()));
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target) && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet delta = propagate(pointer, entry.pointsToSet());
            if (delta.isEmpty()) {
                continue;
            }
            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    for (StoreField store : var.getStoreFields()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(store.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, store.getFieldRef().resolve()));
                    }
                    for (LoadField load : var.getLoadFields()) {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, load.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(load.getLValue()));
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj));
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke callSite : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, callSite);
            Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee);
            if (callGraph.addEdge(edge)) {
                addReachable(callee);
            }
            Var thisVar = callee.getIR().getThis();
            if (thisVar != null) {
                workList.addEntry(pointerFlowGraph.getVarPtr(thisVar), new PointsToSet(recv));
            }
            InvokeExp invokeExp = callSite.getInvokeExp();
            for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                addPFGEdge(pointerFlowGraph.getVarPtr(invokeExp.getArg(i)),
                        pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)));
            }
            if (callSite.getResult() != null) {
                for (Var ret : callee.getIR().getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                            pointerFlowGraph.getVarPtr(callSite.getResult()));
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
