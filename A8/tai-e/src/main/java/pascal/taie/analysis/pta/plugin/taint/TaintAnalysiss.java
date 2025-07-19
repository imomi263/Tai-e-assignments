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

import pascal.taie.util.collection.Maps;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.MultiMap;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    //public Set<Pair<JMethod,Type>> sourcesSet=new HashSet<>();
    //public Set<Pair<JMethod,Integer>> sinkSet=new HashSet<>();
    //public Map<CSVar, PointsToSet> taintPoints=new HashMap<>();
    public MultiMap<CSVar,Invoke> varToInvoke= Maps.newMultiMap();
    //public Set<Obj> taintObjs=new HashSet<>();


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

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        //initBuildTaint();

        checkTaintFlows(taintFlows);
        return taintFlows;
    }

    private void checkTaintFlows(Set<TaintFlow> taintFlows) {
        PointerAnalysisResult result = solver.getResult();
        List<CSMethod> lists = result.getCSCallGraph().reachableMethods().toList();
        for(CSMethod m : lists) {
            Set<CSCallSite> css = result.getCSCallGraph().getCallersOf(m);
            for(CSCallSite cs : css) {
                for(int i=0;i<cs.getCallSite().getInvokeExp().getArgCount();i++){
                    Var args = cs.getCallSite().getInvokeExp().getArg(i);
                    if(config.getSinks().contains(new Sink(m.getMethod(),i))){
                        int finalI = i;
                        result.getPointsToSet(csManager.getCSVar(cs.getContext(),args)).forEach(point->{
                            if(manager.isTaint(point.getObject())){
                                taintFlows.add(new TaintFlow(manager.getSourceCall(point.getObject()),cs.getCallSite(), finalI));
                            }
                        });
                    }
                }
//                for(Sink s:config.getSinks()) {
//                    if(cs.getCallSite().getInvokeExp().getArgCount()<=s.index()){
//                        // index从0开始的，所以要参数量<=index的值来判断
//                        return;
//                    }
//                    Var args = cs.getCallSite().getInvokeExp().getArg(s.index());
//                    if(s.method().getSubsignature().equals(m.getMethod().getSubsignature())) {
//                        result.getPointsToSet(csManager.getCSVar(cs.getContext(),args)).forEach(point->{
//                            if(manager.isTaint(point.getObject())){
//                                taintFlows.add(new TaintFlow(manager.getSourceCall(point.getObject()),cs.getCallSite(),s.index()));
//                            }
//                        });
//                    }
//                }
            }
        }
    }

//    private void initBuildTaint() {
//        config.getSources().forEach(source -> {
//            Pair<JMethod,Type> pair= new Pair<>(source.method(), source.type());
//            sourcesSet.add(pair);
//        });
//        config.getSinks().forEach(sink -> {
//            Pair<JMethod,Integer> pair =new Pair<>(sink.method(),sink.index());
//            sinkSet.add(pair);
//        });
//    }

    public void handleStmt(Invoke invoke, Context context) {

        JMethod resolve = invoke.getMethodRef().resolve();
        for(Source source: config.getSources()){

            if(source.equals(new Source(resolve, resolve.getReturnType()))){
                Obj taintObj = manager.makeTaint(invoke,resolve.getReturnType());
                Var var = invoke.getLValue();
                if(taintObj!=null && var !=null){
                    solver.addWorkList(
                            csManager.getCSVar(context,var),
                            PointsToSetFactory.make(csManager.getCSObj(emptyContext,taintObj))
                    );
                }
            }
        }
//        Type type = resolve.getReturnType();
//        //Pair<JMethod,Type> pair= new Pair<>(resolve, type);
//        if(!config.getSources().contains(new Source(resolve,type))){
//            return null;
//        }
//        Obj obj = manager.makeTaint(invoke,type);
//        taintObjs.add(obj);

    }

    public void transferTaint(JMethod m,CSVar base,CSCallSite csCallSite) {
        PointerAnalysisResult result = solver.getResult();

        // base-to-return
        if(base!=null && csCallSite.getCallSite().getLValue() != null &&
                config.getTransfers().contains(new TaintTransfer(m,TaintTransfer.BASE,TaintTransfer.RESULT,m.getReturnType()))){
            // 返回值
            CSVar csVar = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getLValue());
            result.getPointsToSet(base).forEach(point -> {
                if(manager.isTaint(point.getObject())){
                    Invoke invoke = manager.getSourceCall(point.getObject());
                    Obj o=manager.makeTaint(invoke,m.getReturnType()); // 这里应该是类型可能会发生改变
                    solver.addWorkList(csVar,PointsToSetFactory.make(csManager.getCSObj(emptyContext,o)));
                }
            });
        }

        // arg-to-return
        for(int i=0;i<csCallSite.getCallSite().getInvokeExp().getArgCount();i++){
            if(csCallSite.getCallSite().getLValue()!=null && config.getTransfers().contains(
                    new TaintTransfer(m,i,TaintTransfer.RESULT,m.getReturnType()))){
                CSVar csVar =csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getLValue());
                result.getPointsToSet(csManager.getCSVar(csCallSite.getContext(),
                                csCallSite.getCallSite().getInvokeExp().getArg(i))).forEach(point -> {
                    if(manager.isTaint(point.getObject())){
                        Invoke invoke = manager.getSourceCall(point.getObject());
                        Obj o=manager.makeTaint(invoke,m.getReturnType());
                        solver.addWorkList(csVar,PointsToSetFactory.make(csManager.getCSObj(emptyContext,o)));
                    }
                });
            }
        }

        // arg-to-base
        for(int i=0;i<csCallSite.getCallSite().getInvokeExp().getArgCount();i++){
            if(base!=null && config.getTransfers().contains(new TaintTransfer(m,i,TaintTransfer.BASE, base.getType()))){
                result.getPointsToSet(csManager.getCSVar(csCallSite.getContext(),
                        csCallSite.getCallSite().getInvokeExp().getArg(i))).forEach(point -> {
                    if(manager.isTaint(point.getObject())){
                        Invoke invoke = manager.getSourceCall(point.getObject());
                        Obj o=manager.makeTaint(invoke,base.getType());
                        solver.addWorkList(
                                csManager.getCSVar(csCallSite.getContext(), base.getVar()),
                                PointsToSetFactory.make(csManager.getCSObj(emptyContext,o))
                        );
                    }
                });
            }
        }
//        Var var =csVar.getVar();
//        for(Invoke invoke:varToInvoke.get(csVar)){
//            JMethod method = invoke.getMethodRef().resolve();
//            InvokeExp invokeExp = invoke.getInvokeExp();
//
//            for (TaintTransfer transfer : config.getTransfers()) {
//                JMethod m = transfer.method();
//                int from = transfer.from();
//                int to = transfer.to();
//                Type type = transfer.type();
//                Var taint;
//                if(method.equals(m) && method.getReturnType().equals(type)){
//                    // 找到方法了
//                    if(to == -2){
//                        // return
//                        taint = invoke.getLValue();
//                    }else if(to == -1){
//                        if( invokeExp instanceof InvokeInstanceExp exp){
//                            taint = exp.getBase();
//                        }else{
//                            taint = null;
//                            assert(false);
//                        }
//                    }else{
//                        taint = invokeExp.getArg(to);
//                    }
//                    if(from>=0){
//                        // 参数
//                        if(invokeExp.getArg(from).equals(var)){
//                            taintPoints.get(csVar).forEach(obj->{
//                                // 把csVar指向的添加到taint指向的了
//                                taintPoints.put(csManager.getCSVar(csVar.getContext(), taint),
//                                        PointsToSetFactory.make(obj));
//                            });
//
//                        }
//                    }
//                    if(from <0 && invoke.getInvokeExp() instanceof InvokeInstanceExp exp){
//                        Var base = exp.getBase();
//                        CSVar cs = csManager.getCSVar(csVar.getContext(), base);
//                        if(taintPoints.get(cs)!=null && !taintPoints.get(cs).isEmpty() && from == -1 && to ==-2){
//                            // base -> return
//                            Var lvalue = invoke.getLValue();
//                            if(lvalue == null) return;
//                            taintPoints.get(cs).forEach(obj->{
//                                // 把csVar指向的添加到taint指向的了
//                                taintPoints.put(csManager.getCSVar(csVar.getContext(), lvalue),
//                                        PointsToSetFactory.make(obj));
//                            });
//
//                        }
//                    }
//                }
//            }
//
//
//        }
    }
}
