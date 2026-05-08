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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.poll();
            if (!callGraph.addReachableMethod(method)) {
                continue;
            }
            method.getIR().stmts()
                    .filter(stmt -> stmt instanceof Invoke)
                    .map(stmt -> (Invoke) stmt)
                    .forEach(callSite -> {
                Set<JMethod> callees = resolve(callSite);
                callees.forEach(callee -> {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
                    if (!callGraph.contains(callee)) {
                        workList.add(callee);
                    }
                });
                    });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> callees = new HashSet<>();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        if (callSite.isStatic()) {
            JMethod callee = dispatch(callSite.getMethodRef().getDeclaringClass(), subsignature);
            if (callee != null) callees.add(callee);
        } else if (callSite.isSpecial()) {
            JMethod callee = dispatch(callSite.getMethodRef().getDeclaringClass(), subsignature);
            if (callee != null) callees.add(callee);
        } else {
            Queue<JClass> classes = new ArrayDeque<>();
            classes.add(callSite.getMethodRef().getDeclaringClass());
            while (!classes.isEmpty()) {
                JClass clazz = classes.poll();
                JMethod target = dispatch(clazz, subsignature);
                if (target != null && !target.isAbstract()) {
                    callees.add(target);
                }
                if (clazz.isInterface()) {
                    classes.addAll(hierarchy.getDirectSubinterfacesOf(clazz));
                    classes.addAll(hierarchy.getDirectImplementorsOf(clazz));
                } else {
                    classes.addAll(hierarchy.getDirectSubclassesOf(clazz));
                }
            }
        }
        return callees;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null) {
            return method;
        }
        JClass superClass = jclass.getSuperClass();
        return superClass == null ? null : dispatch(superClass, subsignature);
    }
}
