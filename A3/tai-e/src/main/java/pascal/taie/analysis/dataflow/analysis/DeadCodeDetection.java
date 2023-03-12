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
import pascal.taie.util.collection.Pair;

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
        // Your task is to recognize dead code in ir and add it to deadCode
        Map<Stmt, Boolean> visited = new HashMap<>();
        for (Stmt node : cfg) {
            visited.put(node, false);
        }
        Queue<Stmt> q = new ArrayDeque<>();
        q.add(cfg.getEntry());
        visited.put(cfg.getEntry(), true);
        while (!q.isEmpty()) {
            Stmt p = q.poll();
            if (p instanceof If ifStmt) {
                Value condition = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(p));
                if (condition.isConstant()) { //如果 if语句的条件是一个（可判断的）常量
                    if (condition.getConstant() == 1) {//如果 是true常量
                        //那么 if语句的true分支不是dead code
                        if (!visited.get(ifStmt.getTarget())) {
                            q.add(ifStmt.getTarget());
                            visited.put(ifStmt.getTarget(), true);
                        }
                    } else {//如果 是false常量
                        //那么 if语句的false分支不是dead code
                        cfg.getOutEdgesOf(p).forEach(edge -> {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                if (!visited.get(edge.getTarget())) {
                                    q.add(edge.getTarget());
                                    visited.put(edge.getTarget(), true);
                                }
                            }
                        });
                    }
                    continue;
                }
            } else if (p instanceof SwitchStmt switchStmt) {
                Value condition = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(p));
                if (condition.isConstant()) {//如果 switch语句的条件是一个（可判断的）常量
                    List<Pair<Integer, Stmt>> cases = switchStmt.getCaseTargets();
                    boolean found = false;
                    for (Pair<Integer, Stmt> c : cases) {
                        if (c.first() == condition.getConstant()) {//如果 该常量是某个case之一，标记该case分支为非dead code
                            if (!visited.get(c.second())) {
                                q.add(c.second());
                                visited.put(c.second(), true);
                            }
                            found = true;
                            break;
                        }
                    }
                    if (!found) {//否则 标记default分支为非dead code
                        if (!visited.get(switchStmt.getDefaultTarget())) {
                            q.add(switchStmt.getDefaultTarget());
                            visited.put(switchStmt.getDefaultTarget(), true);
                        }
                    }
                    continue;
                }
            } else if (p instanceof AssignStmt<?, ?> assignStmt) {
                LValue lValue = assignStmt.getLValue();
                if (lValue instanceof Var lVar) {
                    if (!liveVars.getOutFact(p).contains(lVar)) {
                        if (hasNoSideEffect(assignStmt.getRValue())) {
                            deadCode.add(p);
                        }
                    }
                }
            }
            cfg.getOutEdgesOf(p).forEach(edge -> {
                if (!visited.get(edge.getTarget())) {
                    q.add(edge.getTarget());
                    visited.put(edge.getTarget(), true);
                }
            });
        }
        for (Stmt node : cfg) {
            if (node != cfg.getExit()) {
                if (!visited.get(node)) {
                    deadCode.add(node);
                }
            }
        }
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
