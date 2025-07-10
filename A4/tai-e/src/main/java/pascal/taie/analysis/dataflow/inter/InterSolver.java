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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me

        for(Node node:icfg){
            if(icfg.getPredsOf(node).isEmpty()){
                //result.setInFact(node,analysis.newBoundaryFact(node));
                result.setOutFact(node,analysis.newBoundaryFact(node));
            }else{
                result.setOutFact(node,analysis.newInitialFact());
            }
            result.setInFact(node,analysis.newInitialFact());
        }
    }

    private void doSolve() {
        // TODO - finish me

        workList = new LinkedList<>();
        // 这里的顺序也不能修改
        // 从最前面那个开始跑
        for(Node node:icfg){
            if(icfg.getPredsOf(node).isEmpty()){
                workList.add(node);
            }
        }
        for(Node node:icfg){
            if(!workList.contains(node)){
                workList.add(node);
            }
        }
//        while(!workList.isEmpty()){
//            Node node = workList.remove();
//
//            Fact in = result.getInFact(node);
//
//            for(ICFGEdge<Node> predEdge : icfg.getInEdgesOf(node)){
//                Node predNode = predEdge.getSource();
//                Fact tmpFact = analysis.transferEdge(predEdge,result.getOutFact(predNode));
//                analysis.meetInto(tmpFact, in);
//            }
//
//            if(analysis.transferNode(node,in,result.getOutFact(node))){
//                // 结果这里的Node节点遍历顺序有关
//                // 于是就当节点更新后，将其前后的节点全部重新跑一遍
//                workList.add(node);
//                workList.addAll(icfg.getPredsOf(node));
//                workList.addAll(icfg.getSuccsOf(node));
//            }
//            //else{
//            //    System.out.println("---------------finished---------"+node+result.getInFact(node)+result.getOutFact(node));
//            //}
//        }
        boolean flag=false;
        while(true){
            for(Node node:icfg){
                boolean t;
                Fact in = result.getInFact(node);

                for(ICFGEdge<Node> predEdge : icfg.getInEdgesOf(node)){
                    Node predNode = predEdge.getSource();
                    //if(!icfg.getSuccsOf(predNode).contains(node)){continue;}
                    Fact tmpFact = analysis.transferEdge(predEdge,result.getOutFact(predNode));
                    analysis.meetInto(tmpFact, in);
                }

                t=analysis.transferNode(node,in,result.getOutFact(node));
                if(t){
                    flag=true;
                }
            }
            if(!flag){
                break;
            }
            flag=false;
        }

    }
}
