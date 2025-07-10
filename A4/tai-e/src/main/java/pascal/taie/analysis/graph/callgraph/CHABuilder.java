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
import pascal.taie.ir.IR;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Stream;

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
        callGraph.addReachableMethod(entry);
        // TODO - finish me

        Set<JMethod> reachableMethods = new HashSet<>();
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        //reachableMethods.add(entry);
        while(!workList.isEmpty()) {
            JMethod current = workList.remove();
            if(!reachableMethods.contains(current)) {
                reachableMethods.add(current);
                IR ir = current.getIR();
                Set<Invoke> invokeSet= new HashSet<>();

                for(Stmt stmt : ir.getStmts()) {
                    if(stmt instanceof Invoke) {
                        invokeSet.add((Invoke)stmt);
                    }
                }

                for(Invoke invoke : invokeSet) {

                    Set<JMethod> resolves = resolve(invoke);
                    resolves.forEach(method ->{
                        // 添加边
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,method));
                        callGraph.addReachableMethod(method);
                        // 添加到工作集
                        workList.add(method);
                    });
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methods = new HashSet<>();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        // <C: T foo(P,Q,R)>
        JClass jClass=callSite.getMethodRef().getDeclaringClass();
        if(callSite.isStatic()) {

            methods.add(hierarchy.getJREMethod("<"+jClass.toString()+": "+subsignature.toString()+">"));
        }
        if(callSite.isSpecial()){
            JClass clazz= callSite.getMethodRef().getDeclaringClass();
            methods.add(dispatch(clazz,subsignature));
        }
        if(callSite.isVirtual()){

            JClass clazz=callSite.getMethodRef().getDeclaringClass();
            Set<JClass> classzSet = new HashSet<>();
            Queue<JClass> queue = new LinkedList<>();
            queue.add(clazz);
            // 找到所有的子类（直接和间接）
            while(!queue.isEmpty()){
                JClass t = queue.remove();
                classzSet.add(t);
                for(JClass c : hierarchy.getDirectSubclassesOf(t)){
                    if(queue.contains(c)){
                        continue;
                    }
                    classzSet.add(c);
                    queue.add(c);
                }
            }
            classzSet.forEach(c->
            {
                methods.add(dispatch(c,subsignature));
            });
        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        Collection<JMethod> declaredMethods = jclass.getDeclaredMethods();
        for(JMethod method : declaredMethods) {
            if(subsignature.equals(method.getSubsignature())) {
                return method;
            }
        }
        if(jclass.getSuperClass() != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
