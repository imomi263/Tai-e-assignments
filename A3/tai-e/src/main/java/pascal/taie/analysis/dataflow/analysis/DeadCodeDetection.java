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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // 先找到哪里不可达
        Stmt entryStmt = cfg.getEntry();
        if(entryStmt==null) {
            return deadCode;
        }
        // 应该先找活的代码，死的是取相反值
        Queue<Stmt>stmtQueue=new LinkedList<>();
        stmtQueue.add(entryStmt);
        while(!stmtQueue.isEmpty()) {
            Stmt stmt=stmtQueue.remove();
            if(liveCode.contains(stmt)) {
                continue;
            }
            // 把该语句添加进去
            liveCode.add(stmt);
            if(stmt instanceof If) {
                ConditionExp exp = ((If)stmt).getCondition();
                Value value = ConstantPropagation.evaluate(exp,constants.getInFact(stmt));
                if(value.isConstant()){
                    if(value.getConstant() == 0){
                        for(Edge<Stmt> edge:cfg.getOutEdgesOf(stmt)){
                            if(edge.getKind() == Edge.Kind.IF_FALSE){
                                // 把活的那个添加进去
                                //liveCode.add(edge.getTarget());
                                stmtQueue.add(edge.getTarget());
                            }
                        }
                    }else{
                        for(Edge<Stmt> edge:cfg.getOutEdgesOf(stmt)){
                            if(edge.getKind() == Edge.Kind.IF_TRUE){
                                //liveCode.add(edge.getTarget());
                                stmtQueue.add(edge.getTarget());
                            }
                        }
                    }
                }else{
                    // 这里不是固定的，就都添加进去
                    cfg.getOutEdgesOf(stmt).forEach(edge->{
                        //liveCode.add(edge.getTarget());
                        stmtQueue.add(edge.getTarget());
                    });
                }
            }else if(stmt instanceof SwitchStmt) {
                SwitchStmt t=(SwitchStmt)stmt;
                Value value=ConstantPropagation.evaluate(t.getVar(),constants.getInFact(stmt));
                if(value.isConstant()){
                    boolean f=false;
                    for(Edge<Stmt> edge:cfg.getOutEdgesOf(stmt)){
                        if(edge.getKind() == Edge.Kind.SWITCH_CASE){
                            int num=edge.getCaseValue();
                            if(value.getConstant() == num){
                                f=true;
                                //liveCode.add(edge.getTarget());
                                stmtQueue.add(edge.getTarget());
                            }
                        }
                    }
                    if(!f){
                        //liveCode.add(((SwitchStmt) stmt).getDefaultTarget());
                        stmtQueue.add(((SwitchStmt) stmt).getDefaultTarget());
                    }
                }else{
                    // switch语句不是固定的
                    for(Edge<Stmt> edge:cfg.getOutEdgesOf(stmt)){
                        //liveCode.add(edge.getTarget());
                        stmtQueue.add(edge.getTarget());
                    }
                }
            }else{
                // 不是分支语句，就把所有后续的语句都添加进去
                //liveCode.add(t);
                stmtQueue.addAll(cfg.getSuccsOf(stmt));

            }
        }
        // 已经找到了所有的活语句
        // 不在活语句的加入到死代码中
        for(Stmt stmt:cfg.getNodes()){
            if(!liveCode.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

        // 接下来寻找无用赋值语句
        for(Stmt stmt:cfg.getNodes()){
            if(stmt instanceof AssignStmt) {
                AssignStmt t=(AssignStmt)stmt;
                LValue lvalue = t.getLValue();
                RValue rvalue = t.getRValue();
                if(!liveVars.getOutFact(stmt).contains((Var)lvalue)) {
                    if(hasNoSideEffect(rvalue)) {
                        deadCode.add(stmt);
                    }
                }
            }
        }
//        Queue<Stmt> stmtQueue = new LinkedList<>();
//        stmtQueue.add(entryStmt);
//        while(!stmtQueue.isEmpty()) {
//            entryStmt = stmtQueue.remove();
//            if(deadCode.contains(entryStmt)) {
//                //stmtQueue.addAll(cfg.getSuccsOf(entryStmt));
//                continue;
//            }
//
//            if(deadCode.containsAll(cfg.getPredsOf(entryStmt))){
//                // 一个语句的所有前面的语句都是死代码，该语句也是死代码
//                deadCode.add(entryStmt);
//            }
//            if(entryStmt instanceof If){
//                ConditionExp exp = ((If)entryStmt).getCondition();
//                Value value = ConstantPropagation.evaluate(exp,constants.getInFact(entryStmt));
//                if(value.isConstant()){
//                    if(value.getConstant() == 0){
//                        // 这里是为假，为真的语句就添加到死代码里面
//                        for(Edge<Stmt> edge:cfg.getOutEdgesOf(entryStmt)){
//                            if(edge.getKind() == Edge.Kind.IF_TRUE){
//                                deadCode.add(edge.getTarget());
//                                // 把所有的都添加进去
//                                stmtQueue.addAll(cfg.getSuccsOf(entryStmt));
//                            }
//                        }
//                    }else{
//                        for(Edge<Stmt> edge:cfg.getOutEdgesOf(entryStmt)){
//                            if(edge.getKind() == Edge.Kind.IF_FALSE){
//                                deadCode.add(edge.getTarget());
//                                stmtQueue.addAll(cfg.getSuccsOf(entryStmt));
//                            }
//                        }
//                    }
//                }
//            }
//            if(entryStmt instanceof SwitchStmt){
//                SwitchStmt t=(SwitchStmt)entryStmt;
//                Value value=ConstantPropagation.evaluate(t.getVar(),constants.getInFact(entryStmt));
//                for(Edge<Stmt> edge:cfg.getOutEdgesOf(entryStmt)){
//                    if(edge.getKind() == Edge.Kind.SWITCH_CASE){
//                        int num=edge.getCaseValue();
//
//                    }
//                }
//            }
//        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
