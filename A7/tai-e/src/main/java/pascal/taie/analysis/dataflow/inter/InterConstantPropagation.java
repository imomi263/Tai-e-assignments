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

import jas.Pair;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;


    public Map<Var,Set<Var>> aliasSet;
    public HashMap<Pair<?,?>, Value> valMap = new HashMap<>(); // alias-relative values
    public HashMap<Pair<JClass, FieldRef>, HashSet<LoadField>> staticLoadMap = new HashMap<>(); // maintain relative static field

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        aliasSet = new HashMap<>();
        valMap = new HashMap<>();
        staticLoadMap = new HashMap<>();
        buildAlias();
        buildStaticAlias();
    }

    private void buildStaticAlias() {
        for(Stmt stmt:icfg.getNodes()){
            if(stmt instanceof LoadField loadField){
                if(loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess){
                    JClass jClass = staticFieldAccess.getFieldRef().getDeclaringClass();
                    FieldRef fieldRef = staticFieldAccess.getFieldRef();
                    // 这里只会在使用T.f赋值的时候会影响到左边的值，进而影响整个过程
                    staticLoadMap.getOrDefault(new Pair<>(jClass,fieldRef),new HashSet<>()).add(loadField);
                }
            }
        }
    }

    private void buildAlias() {
        Collection<Var> vars = pta.getVars().stream().toList();
        for(Var var1 : vars) {

            Set<Var> st=aliasSet.getOrDefault(var1, new HashSet<>());
            st.add(var1);

            Set<Obj> pointsToSet1 = pta.getPointsToSet(var1);
            for(Var var2:vars){
                Set<Obj> pointsToSet = pta.getPointsToSet(var2);
                if(!Collections.disjoint(pointsToSet1, pointsToSet)){
                    // 有交集
                    st.add(var2);
                }
            }
            aliasSet.put(var1, st);
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
        // TODO - finish me

        if(in.equals(out)){
            return false;
        }else{
            out.clear();
            in.forEach(out::update);
            return true;
        }

    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        AtomicBoolean changed = new AtomicBoolean(false);

        if(stmt instanceof StoreField storeField){
            FieldAccess fieldAccess = storeField.getFieldAccess();
            if(fieldAccess instanceof StaticFieldAccess staticFieldAccess){

                Pair<JClass,FieldRef> key = new Pair<>(staticFieldAccess.getFieldRef().getDeclaringClass(),
                        staticFieldAccess.getFieldRef());
                Value oldValue=valMap.getOrDefault(key,Value.getUndef());
                Var rValue = storeField.getRValue();
                Value newValue= cp.meetValue(oldValue,evaluate(rValue,in));
                valMap.put(key,newValue);

                solver.workList.addAll(staticLoadMap.getOrDefault(key, new HashSet<>()));
                if(!newValue.equals(oldValue)){
                    changed.set(true);
                }

            }else if(fieldAccess instanceof InstanceFieldAccess instanceFieldAccess){
                Var base = instanceFieldAccess.getBase();
                pta.getPointsToSet(base).forEach(obj->{
                    Pair<Obj,FieldRef> key = new Pair<>(obj,instanceFieldAccess.getFieldRef());
                    Value oldValue=valMap.getOrDefault(key,Value.getUndef());
                    Var rValue = storeField.getRValue();
                    Value newValue= cp.meetValue(oldValue,evaluate(rValue,in));
                    valMap.put(key,newValue);


                    for (Var var : aliasSet.getOrDefault(base, new HashSet<>())) {
                        solver.workList.addAll(var.getLoadFields());
                    }

                    if(!newValue.equals(oldValue)){
                        changed.set(true);
                    }
                });
            }
        }else if (stmt instanceof StoreArray storeArray){
            Var base = storeArray.getArrayAccess().getBase();
            Var index = storeArray.getArrayAccess().getIndex();
            Value indexValue = evaluate(index,in);
            if(!(indexValue.isUndef() || !cp.canHoldInt(index))){

                pta.getPointsToSet(base).forEach(obj->{
                    Pair<Obj,Value> key = new Pair<>(obj,indexValue);
                    Value oldValue=valMap.getOrDefault(key,Value.getUndef());

                    Var rValue = storeArray.getRValue();

                    Value newValue= cp.meetValue(oldValue,evaluate(rValue,in));
                    valMap.put(key,newValue);

                    for (Var var : aliasSet.getOrDefault(base, new HashSet<>())) {
                        solver.workList.addAll(var.getLoadArrays());
                    }

                    if(!newValue.equals(oldValue)){
                        changed.set(true);
                    }
                });
            }

        }

        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);
        if(stmt instanceof DefinitionStmt defStmt){
            LValue lValue = defStmt.getLValue();
            if(lValue instanceof Var var&& cp.canHoldInt(var)){
                out.remove(var);
                if(defStmt.getRValue()!=null){
                    Value gen = evaluate(defStmt.getRValue(), in);
                    if(gen!=null)
                        out.update(var,gen);
                }

            }
        }
        if(!out.equals(old)){
            changed.set(true);
        }
        return changed.get();
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        // 这里是不变的
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        // x=m()，干掉左边的值
        CPFact ans =out.copy();
        Stmt source = edge.getSource();
        if(source.getDef().isEmpty()){
            return ans;
        }else{
            ans.remove((Var)source.getDef().get());
        }
        return ans;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact ans = new CPFact();
        JMethod callee = edge.getCallee();
        Stmt source = edge.getSource();
        List<Var> params = callee.getIR().getParams();

        for(int t=0;t<params.size();t++) {
            if(source instanceof Invoke invoke){
                Var paramEr=invoke.getInvokeExp().getArg(t);
                //Var paramEr = (Var)source.getUses().get(t);
                Var paramEe = params.get(t);
                ans.update(paramEe,callSiteOut.get(paramEr));
            }

        }
        return ans;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact ans = new CPFact();
        // 如果有多个返回值，应该是返回NAC
        Collection<Var> returnVars = edge.getReturnVars();
        Stmt stmt=edge.getCallSite();
        Value tmp=Value.getUndef();
        for(Var returnVar : returnVars) {
            tmp=cp.meetValue(tmp,returnOut.get(returnVar));
        }
        Optional<LValue> lvalue = stmt.getDef();
        if(lvalue.isPresent()){
            ans.update((Var) lvalue.get(), tmp);
        }

        return ans;
    }

    private Value evaluate(Exp exp, CPFact in) {
        if(exp instanceof StaticFieldAccess staticFieldAccess){
            JClass declaringClass = staticFieldAccess.getFieldRef().getDeclaringClass();
            FieldRef fieldRef = staticFieldAccess.getFieldRef();
            Pair<JClass,FieldRef> pair = new Pair<>(declaringClass,fieldRef);
            Value ans = valMap.getOrDefault(pair, Value.getUndef());
            return ans;
        }else if(exp instanceof InstanceFieldAccess instanceFieldAccess){
            Var base = instanceFieldAccess.getBase();
            FieldRef fieldRef = instanceFieldAccess.getFieldRef();
            Value ans = Value.getUndef();
            for(Obj obj:pta.getPointsToSet(base)){
                ans = cp.meetValue(ans,valMap.getOrDefault(new Pair<>(obj, fieldRef), Value.getUndef()));
            }
            return ans;
        }else if(exp instanceof ArrayAccess arrayAccess){
            Var base = arrayAccess.getBase();
            Value index = cp.evaluate(arrayAccess.getIndex(),in);
            Value ans = Value.getUndef();
            for(Obj obj:pta.getPointsToSet(base)){
                // 这里和NAC的也是别名，于是就meetValue一下，不知道是否正确
                // 这里我觉得当获取一个值后，由于可能和NAC也是别名，就执行meetValue操作
                // 这样可以通过其中一个测试点
                // 这里如果是NAC，则需要对该obj所有其他index进行判断，例如<obj,1>等
                if(index.isConstant()){
                    Value value=valMap.getOrDefault(new Pair<>(obj, index), Value.getUndef());
                    value = cp.meetValue(value,valMap.getOrDefault(new Pair<>(obj,Value.getNAC()),Value.getUndef()));
                    ans = cp.meetValue(ans,value);
                }else if(index.isNAC()){
                    Value value=valMap.getOrDefault(new Pair<>(obj, index), Value.getUndef());
                    for (Map.Entry<Pair<?, ?>, Value> pairValueEntry : valMap.entrySet()) {
                        if(pairValueEntry.getKey().getO1().equals(obj)){
                            if(pairValueEntry.getKey().getO2() instanceof Value){
                                value = cp.meetValue(value,((Value)pairValueEntry.getKey().getO2()));
                            }
                        }
                    }
                    ans = cp.meetValue(ans,value);
                }
            }
            return ans;
        }else{
            return cp.evaluate(exp,in);
        }
    }
}


