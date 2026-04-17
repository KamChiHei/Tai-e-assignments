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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        CPFact fact = new CPFact();
        IR ir = cfg.getIR();
        for (Var param : ir.getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value) ->
                target.update(var, meetValue(value, target.get(var))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        return v1.equals(v2) ? v1 : Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        out.clear();
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?, ?> defStmt &&
                defStmt.getLValue() instanceof Var lVar &&
                canHoldInt(lVar)) {
            Exp rValue = (Exp) defStmt.getRValue();
            out.update(lVar, evaluate(rValue, in));
        }
        return !out.equals(oldOut);
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
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof Var var) {
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        }
        if (exp instanceof BinaryExp binaryExp) {
            Var operand1 = binaryExp.getOperand1();
            Var operand2 = binaryExp.getOperand2();
            Value v1 = canHoldInt(operand1) ? in.get(operand1) : Value.getNAC();
            Value v2 = canHoldInt(operand2) ? in.get(operand2) : Value.getNAC();
            BinaryExp.Op op = binaryExp.getOperator();
            if (op instanceof ArithmeticExp.Op aop &&
                    (aop == ArithmeticExp.Op.DIV || aop == ArithmeticExp.Op.REM) &&
                    v2.isConstant() && v2.getConstant() == 0) {
                return Value.getUndef();
            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }
            int c1 = v1.getConstant();
            int c2 = v2.getConstant();
            if (op instanceof ArithmeticExp.Op aop) {
                return switch (aop) {
                    case ADD -> Value.makeConstant(c1 + c2);
                    case SUB -> Value.makeConstant(c1 - c2);
                    case MUL -> Value.makeConstant(c1 * c2);
                    case DIV -> Value.makeConstant(c1 / c2);
                    case REM -> Value.makeConstant(c1 % c2);
                };
            } else if (op instanceof ConditionExp.Op cop) {
                return switch (cop) {
                    case EQ -> Value.makeConstant(c1 == c2 ? 1 : 0);
                    case NE -> Value.makeConstant(c1 != c2 ? 1 : 0);
                    case LT -> Value.makeConstant(c1 < c2 ? 1 : 0);
                    case GT -> Value.makeConstant(c1 > c2 ? 1 : 0);
                    case LE -> Value.makeConstant(c1 <= c2 ? 1 : 0);
                    case GE -> Value.makeConstant(c1 >= c2 ? 1 : 0);
                };
            } else if (op instanceof ShiftExp.Op sop) {
                return switch (sop) {
                    case SHL -> Value.makeConstant(c1 << c2);
                    case SHR -> Value.makeConstant(c1 >> c2);
                    case USHR -> Value.makeConstant(c1 >>> c2);
                };
            } else if (op instanceof BitwiseExp.Op bop) {
                return switch (bop) {
                    case OR -> Value.makeConstant(c1 | c2);
                    case AND -> Value.makeConstant(c1 & c2);
                    case XOR -> Value.makeConstant(c1 ^ c2);
                };
            }
        }
        return Value.getNAC();
    }
}
