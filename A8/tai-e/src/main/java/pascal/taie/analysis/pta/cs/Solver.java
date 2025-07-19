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

package pascal.taie.analysis.pta.cs;

import jas.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Collections;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for(Stmt stmt:csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt){
            Obj obj = heapModel.getObj(stmt);
            Pointer x = csManager.getCSVar(context,stmt.getLValue());
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod,obj),obj);
            PointsToSet pts = PointsToSetFactory.make(csObj);
            workList.addEntry(x,pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt){
            addPFGEdge(csManager.getCSVar(context,stmt.getRValue()),
                    csManager.getCSVar(context,stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt){
            if(!stmt.isStatic()) return null;
            JField jField = stmt.getFieldRef().resolve();
            Var lvar = stmt.getLValue();
            StaticField staticField =csManager.getStaticField(jField);
            Pointer ptr = csManager.getCSVar(context,lvar);
            addPFGEdge(staticField,ptr);
            return null;
        }

        @Override
        public Void visit(StoreField stmt){
            if(!stmt.isStatic()) return null;
            JField jField = stmt.getFieldRef().resolve();
            Var rvar = stmt.getRValue();
            StaticField staticField =csManager.getStaticField(jField);
            Pointer ptr = csManager.getCSVar(context,rvar);
            addPFGEdge(ptr,staticField);
            return null;
        }

//        public void  invokeTaint(Invoke stmt,JMethod callee,Context context){
//            Obj obj=taintAnalysis.handleStmt(stmt,context);
//            CSCallSite csCallSite = csManager.getCSCallSite(context,stmt);
//            Context ct = contextSelector.selectContext(csCallSite, callee);
//            CSMethod csMethod = csManager.getCSMethod(ct, callee);
//            Var lValue=stmt.getLValue();
//            if(obj!=null && lValue!=null){
//                // 处理一开始source的逻辑
//                CSVar v=csManager.getCSVar(context, lValue);
//                CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod,obj),obj);
//                PointsToSet pts = PointsToSetFactory.make(csObj);
//                taintAnalysis.taintPoints.put(v,pts);
//                workList.addEntry(v,pts);
//            }
//            stmt.getInvokeExp().getArgs().forEach(var->{
//                taintAnalysis.varToInvoke.put(csManager.getCSVar(context,var),stmt);
//            });
//        }

        @Override
        public Void visit(Invoke stmt){
            // 预处理加上被source污染的对象
            if(!stmt.isStatic()){
                //invokeTaint(stmt,stmt.getMethodRef().resolve());
                stmt.getInvokeExp().getArgs().forEach(arg->{
                    taintAnalysis.varToInvoke.put(csManager.getCSVar(context,arg),stmt);
                });
                return null;
            }
            JMethod callee = resolveCallee(null,stmt);



            if(!stmt.isStatic()){
                return null;
            }
            Var lvar = stmt.getLValue();

            CSCallSite csCallSite = csManager.getCSCallSite(context,stmt);
            Context ct = contextSelector.selectContext(csCallSite, callee);
            CSMethod csMethod = csManager.getCSMethod(ct, callee);

            if(!callGraph.getCalleesOf(csCallSite).contains(csMethod)){
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),csCallSite,csMethod));
                addReachable(csMethod);

                for(int i=0;i<stmt.getInvokeExp().getArgs().size();i++){
                    Var var1 = stmt.getInvokeExp().getArg(i);
                    Var var2 = callee.getIR().getVar(i);

                    Pointer ptr1 = csManager.getCSVar(context,var1);
                    Pointer ptr2 = csManager.getCSVar(ct,var2);
                    addPFGEdge(ptr1,ptr2);
                }

                if(lvar ==null || callee.getIR().getReturnVars().isEmpty()){
                    return null;
                }
                callee.getIR().getReturnVars().forEach(var ->{
                    //System.out.println("--------------"+var);
                    addPFGEdge(csManager.getCSVar(ct,var),csManager.getCSVar(context,lvar));
                });

                taintAnalysis.handleStmt(stmt, csCallSite.getContext());
                taintAnalysis.transferTaint(callee,null,csCallSite);

                stmt.getInvokeExp().getArgs().forEach(arg->{
                    taintAnalysis.varToInvoke.put(csManager.getCSVar(context,arg),stmt);
                });
            }

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(!pointerFlowGraph.addEdge(source,target)){

        }
        // 这里由于污点传播可能会出现source指向的对象集合变多
        // 所有不能根据是否添加过这个条件判断要不要增加到工作集合中
        if(!source.getPointsToSet().isEmpty()){
            workList.addEntry(target,source.getPointsToSet());
        }
//        if(source instanceof CSVar csVar){
//            PointsToSet csObjs = taintAnalysis.taintPoints.get(csVar);
//            if(csObjs == null){
//                return;
//            }else{
//                if(target instanceof CSVar c){
//                    workList.addEntry(c,csObjs);
//                    taintAnalysis.taintPoints.put(c,csObjs);
//                }
//
//            }
//        }
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

            if(pt instanceof CSVar csVar){
                Var var =(csVar).getVar();
                Context context = (csVar).getContext();

                var.getLoadFields().forEach(loadField->{
                    if(loadField.isStatic()){
                        return;
                    }
                    CSVar ptr1 = csManager.getCSVar(context,loadField.getLValue());
                    InstanceField ptr2=null;
                    for(CSObj o:delta.getObjects()){
                        ptr2=csManager.getInstanceField(o,loadField.getFieldRef().resolve());
                        addPFGEdge(ptr2,ptr1);
                    }
                });

                var.getStoreFields().forEach(storeField->{
                    if(storeField.isStatic()){
                        return;
                    }
                    CSVar ptr1 = csManager.getCSVar(context,storeField.getRValue());
                    InstanceField ptr2=null;
                    for(CSObj o:delta.getObjects()){
                        ptr2=csManager.getInstanceField(o,storeField.getFieldRef().resolve());
                        addPFGEdge(ptr1,ptr2);
                    }
                });

                var.getLoadArrays().forEach(loadArray->{
                    // y=x[i];
                    CSVar ptr1 = csManager.getCSVar(context,loadArray.getLValue());
                    ArrayIndex ptr2=null;
                    for(CSObj o:delta.getObjects()){
                        ptr2=csManager.getArrayIndex(o);
                        addPFGEdge(ptr2,ptr1);
                    }
                });

                var.getStoreArrays().forEach(storeArray->{
                    // x[i]=y;
                    CSVar ptr1 = csManager.getCSVar(context,storeArray.getRValue());
                    ArrayIndex ptr2=null;
                    for(CSObj o:delta.getObjects()){
                        ptr2=csManager.getArrayIndex(o);
                        addPFGEdge(ptr1,ptr2);
                    }
                });

                taintAnalysis.varToInvoke.get(csVar).forEach(invoke ->
                {
                    CSCallSite csCallSite = csManager.getCSCallSite(context,invoke);
                    if(invoke.getInvokeExp() instanceof InvokeInstanceExp invokeExp){
                        CSVar recv = csManager.getCSVar(context,invokeExp.getBase());
                        result.getPointsToSet(recv).forEach(recvObj ->{
                            JMethod method = resolveCallee(recvObj,invoke);
                            taintAnalysis.transferTaint(method,recv,csCallSite);
                        });
                    }else{
                        JMethod method = resolveCallee(null,invoke);
                        taintAnalysis.transferTaint(method,null,csCallSite);
                    }
                });

                delta.getObjects().forEach(obj->{
                    processCall(((CSVar) pt),obj);
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
        PointsToSet delta = PointsToSetFactory.make();
        for(CSObj p :pointsToSet.getObjects()){
            if(!pointer.getPointsToSet().contains(p)){
                delta.addObject(p);
                //pointer.getPointsToSet().addObject(p);
            }
        }
        if(delta.isEmpty()){
            return delta;
        }
        for(CSObj p :delta.getObjects()){
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var var = recv.getVar();
        Context c = recv.getContext();
        for(Invoke invoke:var.getInvokes()){
            JMethod method = resolveCallee(recvObj,invoke);
            CSCallSite cs = csManager.getCSCallSite(c,invoke);
            Context context= contextSelector.selectContext(cs,recvObj,method);
            // 传入this指针
            workList.addEntry(csManager.getCSVar(context,method.getIR().getThis()), PointsToSetFactory.make(recvObj));

            if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),cs,
                    csManager.getCSMethod(context,method)))){
                addReachable(csManager.getCSMethod(context,method));

                for(int i=0;i< method.getParamCount();i++){
                    Var var1=method.getIR().getParam(i);
                    var var2=invoke.getInvokeExp().getArg(i);
                    assert var1!=null && var2!=null;
                    addPFGEdge(csManager.getCSVar(c,var2),csManager.getCSVar(context,var1));
                }

                Var var3=invoke.getResult();

                method.getIR().getReturnVars().forEach(returnVar->{

                    if(returnVar == null || var3==null){
                        //System.out.println("-----"+invoke.toString());
                        return;
                    }
                    addPFGEdge(csManager.getCSVar(context,returnVar),csManager.getCSVar(c,var3));
                });
            }

            taintAnalysis.handleStmt(invoke,cs.getContext());
            taintAnalysis.transferTaint(method,recv,cs);
        }
    }

    public void addWorkList(Pointer pointer,PointsToSet pointsToSet) {
        workList.addEntry(pointer,pointsToSet);
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
