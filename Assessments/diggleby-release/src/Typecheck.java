import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ast.*;

public class Typecheck {

    private void checkType(Type expected, Type actual) {
        if (!actual.equals(expected)) {
            throw new TypeErrorException(String.format("Type mismatch: Expected %s but got %s", expected, actual));
        }
    }

    public Type typecheckExpr(Map<String, FnDef> fnDefs, Environment<Type> tyEnv, Expr e) {
        // Handle literals
        if (e instanceof EInt) {
            return TyInt.type();
        } else if (e instanceof EBool) {
            return TyBool.type();
        } else if (e instanceof EString) {
            return TyString.type();
        } else if (e instanceof EUnit) {
            return TyUnit.type();
        } 
        // Handle variables
        else if (e instanceof EVar) {
            String varName = ((EVar) e).getVar();
            return tyEnv.lookup(varName);
        } 
        // Handle binary operations
        else if (e instanceof EBinOp) {
            EBinOp binOp = (EBinOp) e;
            Type t1 = typecheckExpr(fnDefs, tyEnv, binOp.getE1());
            Type t2 = typecheckExpr(fnDefs, tyEnv, binOp.getE2());
            
            switch (binOp.getOp()) {
                // Arithmetic operations require Int operands and return Int
                case ADD: case SUB: case MUL: case DIV: case MOD:
                    checkType(TyInt.type(), t1);
                    checkType(TyInt.type(), t2);
                    return TyInt.type();
                
                // Comparison operations require Int operands and return Bool
                case LT: case GT:
                    checkType(TyInt.type(), t1);
                    checkType(TyInt.type(), t2);
                    return TyBool.type();
                
                // Equality can compare any types but they must match
                case EQ:
                    if (!t1.equals(t2)) {
                        throw new TypeErrorException(
                            String.format("Type mismatch in equality comparison: %s and %s", t1, t2));
                    }
                    return TyBool.type();
                
                // Logical operations require Bool operands and return Bool
                case AND: case OR:
                    checkType(TyBool.type(), t1);
                    checkType(TyBool.type(), t2);
                    return TyBool.type();
                    
                default:
                    throw new TypeErrorException("Unknown binary operator: " + binOp.getOp());
            }
        } 
        // Handle NOT operator
        else if (e instanceof ENot) {
            ENot not = (ENot) e;
            Type exprType = typecheckExpr(fnDefs, tyEnv, not.getExpr());
            checkType(TyBool.type(), exprType);
            return TyBool.type();
        } 
        // Handle conditionals (if-then-else)
        else if (e instanceof ECond) {
            ECond cond = (ECond) e;
            Type testType = typecheckExpr(fnDefs, tyEnv, cond.getTest());
            checkType(TyBool.type(), testType);
            
            Type thenType = typecheckExpr(fnDefs, tyEnv, cond.getThenBranch());
            Type elseType = typecheckExpr(fnDefs, tyEnv, cond.getElseBranch());
            
            if (!thenType.equals(elseType)) {
                throw new TypeErrorException(
                    String.format("Type mismatch in if branches: %s and %s", thenType, elseType));
            }
            
            return thenType;
        } 
        // Handle let expressions
        else if (e instanceof ELet) {
            ELet let = (ELet) e;
            Type subjectType = typecheckExpr(fnDefs, tyEnv, let.getSubject());
            Environment<Type> extendedEnv = tyEnv.extend(let.getBinder(), subjectType);
            return typecheckExpr(fnDefs, extendedEnv, let.getContinuation());
        } 
        // Handle function calls
        else if (e instanceof EFnCall) {
            EFnCall fnCall = (EFnCall) e;
            String fnName = fnCall.getFnName();
            
            if (!fnDefs.containsKey(fnName)) {
                throw new TypeErrorException("Undefined function: " + fnName);
            }
            
            FnDef fnDef = fnDefs.get(fnName);
            List<Expr> args = fnCall.getArgs();
            List<AnnotatedParam> params = fnDef.getParams();
            
            if (args.size() != params.size()) {
                throw new TypeErrorException(
                    String.format("Function %s expects %d arguments but got %d", 
                        fnName, params.size(), args.size()));
            }
            
            for (int i = 0; i < args.size(); i++) {
                Type argType = typecheckExpr(fnDefs, tyEnv, args.get(i));
                Type paramType = params.get(i).type;
                checkType(paramType, argType);
            }
            
            return fnDef.getReturnType();
        } 
        // Handle print expressions
        else if (e instanceof EPrint) {
            EPrint print = (EPrint) e;
            // We don't care about the type of what's being printed
            typecheckExpr(fnDefs, tyEnv, print.getExpr());
            return TyUnit.type();
        } 
        // Handle getInput
        else if (e instanceof EGetInput) {
            return TyString.type();
        } 
        // Handle type casts
        else if (e instanceof ECast) {
            ECast cast = (ECast) e;
            Type exprType = typecheckExpr(fnDefs, tyEnv, cast.getExpr());
            Type castType = cast.getType();
            
            // Check if the cast is valid based on language rules
            if ((exprType instanceof TyInt || exprType instanceof TyBool || exprType instanceof TyString) && 
                (castType instanceof TyInt || castType instanceof TyBool || castType instanceof TyString)) {
                return castType;
            } else {
                throw new TypeErrorException(
                    String.format("Invalid cast from %s to %s", exprType, castType));
            }
        } 
        // Handle string concatenation
        else if (e instanceof EConcat) {
            EConcat concat = (EConcat) e;
            List<Expr> exprs = concat.getExprs();
            
            for (Expr expr : exprs) {
                Type exprType = typecheckExpr(fnDefs, tyEnv, expr);
                if (!(exprType instanceof TyString)) {
                    throw new TypeErrorException(
                        String.format("concat requires String arguments, but got %s", exprType));
                }
            }
            
            return TyString.type();
        } 
        else {
            throw new TypeErrorException("Unknown expression type: " + e.getClass().getName());
        }
    }

    public void typecheckDef(Map<String, FnDef> defs, FnDef def) {
        // Create a new environment for this function with its parameters
        Environment<Type> fnEnv = new Environment<>();
        
        // Add each parameter to the environment
        for (AnnotatedParam param : def.getParams()) {
            fnEnv = fnEnv.extend(param.param, param.type);
        }
        
        // Type check the function body
        Type bodyType = typecheckExpr(defs, fnEnv, def.getBody());
        
        // Verify the body type matches the declared return type
        checkType(def.getReturnType(), bodyType);
    }

    public Type typecheckProgram(Program p) {
        // Build map of function definitions for lookup
        Map<String, FnDef> fnDefs = new HashMap<>();
        for (FnDef def : p.getFunctionDefs()) {
            String fnName = def.getFnName();
            if (fnDefs.containsKey(fnName)) {
                throw new TypeErrorException("Duplicate function definition: " + fnName);
            }
            fnDefs.put(fnName, def);
        }
        
        // Type check each function definition
        for (FnDef def : p.getFunctionDefs()) {
            typecheckDef(fnDefs, def);
        }
        
        // Type check the main expression with an empty environment
        return typecheckExpr(fnDefs, new Environment<>(), p.getMainExpr());
    }
}