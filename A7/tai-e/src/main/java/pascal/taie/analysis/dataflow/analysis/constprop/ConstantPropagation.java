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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // 记录已经被定义的变量

        CPFact cpf = new CPFact();

        for(Var v:cfg.getIR().getVars()){
            if (canHoldInt(v)) {
                cpf.update(v,Value.getNAC());
            }
        }
        return cpf;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me

        for(Var var:fact.keySet()){
            if(target.get(var)!=null){
                // 目标里面有这一个
                target.update(var,meetValue(fact.get(var),target.get(var)));
            }else{
                // 目标没有这一个
                target.update(var,fact.get(var));
            }
        }

    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        //System.out.println("meetValue:"+v1+" "+v2);
        if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        else if(v1.isUndef()){
            return v2;
        }
        else if(v2.isUndef()){
            return v1;
        }
        else if(v1.getConstant() == v2.getConstant()){
            return v1;
        }else{
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);
        if(stmt instanceof DefinitionStmt defStmt){
            LValue lValue = defStmt.getLValue();
            if(lValue instanceof Var var&& canHoldInt(var)){
                out.remove(var);
                if(defStmt.getRValue()!=null){
                    Value gen = evaluate(defStmt.getRValue(), in);
                    if(gen!=null)
                        out.update(var,gen);
                }

            }
        }

        return out.equals(old);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish
        if(exp instanceof Var){
            return in.get((Var) exp);
        }
        if (exp instanceof IntLiteral) {
            // 返回一个value
            return Value.makeConstant(((IntLiteral)exp).getValue());
        }
        if(exp instanceof BinaryExp){
            Var var1=((BinaryExp)exp).getOperand1();
            Var var2=((BinaryExp)exp).getOperand2();
            Value value1=in.get(var1);
            Value value2=in.get(var2);
            if(value1.isConstant() && value2.isConstant()){
                if(!canHoldInt(var1) || !canHoldInt(var2)){
                    return Value.getUndef();
                }
                BinaryExp.Op op= ((BinaryExp) exp).getOperator();
                int ans ;
                //int t1=((IntLiteral)var1.getTempConstValue()).getValue();
                //int t2=((IntLiteral)var2.getTempConstValue()).getValue();
                int t1=value1.getConstant();
                int t2=value2.getConstant();
                if(exp instanceof ArithmeticExp){
                    if(op.toString().equals("/") && t2 ==0){
                        return Value.getUndef();
                    }
                    ans = switch (op.toString()) {
                        case "+" -> t1 + t2;
                        case "-" -> t1 - t2;
                        case "*" -> t1 * t2;
                        case "/" -> t1 / t2;
                        default -> t1 % t2;
                    };
                    return Value.makeConstant(ans);
                }
                if (exp instanceof ConditionExp){
                    switch (op.toString()){
                        case "==":
                            if(t1==t2)ans=1;
                            else ans=0;
                            break;
                        case "!=":
                            if(t1!=t2) ans=1;
                            else ans=0;
                            break;
                        case "<":
                            if(t1<t2) ans=1;
                            else ans=0;
                            break;
                        case "<=":
                            if(t1<=t2) ans=1;
                            else ans=0;
                            break;
                        case ">":
                            if(t1>t2) ans=1;
                            else ans=0;
                            break;
                        default:
                            if(t1>=t2) ans=1;
                            else ans=0;
                    }
                    return Value.makeConstant(ans);
                }
                if(exp instanceof ShiftExp){
                    ans = switch (op.toString()) {
                        case "<<" -> t1 << t2;
                        case ">>" -> t1 >> t2;
                        default -> t1 >>> t2;
                    };
                    return Value.makeConstant(ans);
                }
                if(exp instanceof BitwiseExp){
                    ans = switch (op.toString()){
                        case "|" -> t1 | t2;
                        case "^" -> t1 ^ t2;
                        default -> t1 & t2;
                    };
                    return Value.makeConstant(ans);
                }
            }
            else if(value1.isNAC() || value2.isNAC()){
                return Value.getNAC();
            }else{
                return Value.getUndef();
            }

        }
        return Value.getNAC();
    }
}
