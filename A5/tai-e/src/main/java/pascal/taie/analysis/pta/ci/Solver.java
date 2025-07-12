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
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
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
        // TODO - finish me
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            for(Stmt stmt :method.getIR().getStmts()){
                stmtProcessor.visit(stmt);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(Stmt stmt) {
            return stmt.accept(this);
        }

        @Override
        public Void visit(New stmt){
            // x = new T();
            Obj obj = heapModel.getObj(stmt);
            Pointer x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet pts = new PointsToSet(obj);
            workList.addEntry(x, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt){
            // x=y;
            // y->x
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = T.f
            if(!stmt.isStatic()){
                return null;
            }
            // 只处理静态加载
            JField field=stmt.getFieldRef().resolve();
            Var lVar= stmt.getLValue();
            //FieldAccess rValue = stmt.getRValue();

            StaticField field1=pointerFlowGraph.getStaticField(field);
            VarPtr ptr=pointerFlowGraph.getVarPtr(lVar);
            addPFGEdge(field1,ptr);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // T.f = x
            if(!stmt.isStatic()){
                return null;
            }
            JField field=stmt.getFieldRef().resolve();
            Var rVar= stmt.getRValue();
            StaticField field1=pointerFlowGraph.getStaticField(field);
            VarPtr ptr=pointerFlowGraph.getVarPtr(rVar);
            addPFGEdge(ptr,field1);
            return null;
        }


        @Override
        public Void visit(Invoke stmt) {
            // x=T.m(a1,a2,a3)
            if(!stmt.isStatic()){
                return null;
            }

            Var lValue = stmt.getLValue();
            // 没有返回值也可以
            //if(lValue == null){
            //    return null;
            //}
            JMethod callee = resolveCallee(null,stmt);
            // 参数添加约束
            addReachable(callee);
            Var var1;
            Var var2;
            VarPtr ptr1;
            VarPtr ptr2;
            for(int i=0;i<stmt.getInvokeExp().getArgCount();i++){
                var1 = stmt.getInvokeExp().getArg(i);
                var2 = callee.getIR().getParam(i);
                ptr1 = pointerFlowGraph.getVarPtr(var1);
                ptr2 = pointerFlowGraph.getVarPtr(var2);

                addPFGEdge(ptr1,ptr2);
            }
            // 返回值添加边
            if(lValue ==null || callee.getIR().getReturnVars().isEmpty()){
                return null;
            }
            callee.getIR().getReturnVars().forEach(var ->{
                //System.out.println("--------------"+var);
                addPFGEdge(pointerFlowGraph.getVarPtr(var),pointerFlowGraph.getVarPtr(lValue));
            });

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)){
            // 返回为真说明不存在这条边
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me

        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer pt=entry.pointer();
            PointsToSet pts=entry.pointsToSet();

            PointsToSet delta = propagate(pt,pts);

            if(pt instanceof VarPtr){
                Var var =((VarPtr) pt).getVar();

                var.getLoadFields().forEach(loadField->{
                    if(loadField.isStatic()){
                        return;
                    }
                    VarPtr ptr1 = pointerFlowGraph.getVarPtr(loadField.getLValue());
                    InstanceField ptr2=null;
                    for(Obj o:delta.getObjects()){
                        ptr2=pointerFlowGraph.getInstanceField(o,loadField.getFieldRef().resolve());
                        addPFGEdge(ptr2,ptr1);
                    }
                });

                var.getStoreFields().forEach(storeField->{
                    if(storeField.isStatic()){
                        return;
                    }
                    VarPtr ptr1 = pointerFlowGraph.getVarPtr(storeField.getRValue());
                    InstanceField ptr2=null;
                    for(Obj o:delta.getObjects()){
                        ptr2=pointerFlowGraph.getInstanceField(o,storeField.getFieldRef().resolve());
                        addPFGEdge(ptr1,ptr2);
                    }
                });

                var.getLoadArrays().forEach(loadArray->{
                    // y=x[i];
                    VarPtr ptr1 = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                    ArrayIndex ptr2=null;
                    for(Obj o:delta.getObjects()){
                        ptr2=pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(ptr2,ptr1);
                    }
                });

                var.getStoreArrays().forEach(storeArray->{
                    // x[i]=y;
                    VarPtr ptr1 = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                    ArrayIndex ptr2=null;
                    for(Obj o:delta.getObjects()){
                        ptr2=pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(ptr1,ptr2);
                    }
                });


                delta.getObjects().forEach(obj->{
                   processCall(var,obj);
                });

            }


        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
//        if(pointsToSet.isEmpty()){
//            return new PointsToSet();
//        }
        PointsToSet delta = new PointsToSet();
        for(Obj p :pointsToSet.getObjects()){
            if(!pointer.getPointsToSet().contains(p)){
                delta.addObject(p);
                //pointer.getPointsToSet().addObject(p);
            }
        }
        if(delta.isEmpty()){
            return delta;
        }
        for(Obj p :delta.getObjects()){
            pointer.getPointsToSet().addObject(p);
        }
        for(Pointer p:pointerFlowGraph.getSuccsOf(pointer)){
            workList.addEntry(p,pointsToSet);
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
        // TODO - finish me
        // y=x.k(a1,a2,a3)..

        for(Invoke invoke:var.getInvokes()){
            JMethod method = resolveCallee(recv,invoke);

            // 传入this指针
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));

            if(callGraph.addEdge(new Edge<>(CallKind.OTHER,invoke,method))){
                addReachable(method);

                for(int i=0;i< method.getParamCount();i++){
                    Var var1=method.getIR().getParam(i);
                    var var2=invoke.getInvokeExp().getArg(i);
                    assert var1!=null && var2!=null;
                    addPFGEdge(pointerFlowGraph.getVarPtr(var2),pointerFlowGraph.getVarPtr(var1));
                }

                Var var3=invoke.getResult();

                method.getIR().getReturnVars().forEach(returnVar->{

                    if(returnVar == null || var3==null){
                        //System.out.println("-----"+invoke.toString());
                        return;
                    }
                    addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),pointerFlowGraph.getVarPtr(var3));
                });
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
