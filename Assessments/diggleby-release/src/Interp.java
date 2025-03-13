import ast.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

public class Interp {
    private Scanner reader = new Scanner(System.in);

    public Interp() {

    }

    private boolean unwrapBool(Value v) {
        if (v instanceof VBool) {
            return ((VBool) v).getValue();
        } else {
            throw new RuntimeException("Runtime type error: Expected a bool but got value " + v);
        }
    }

    private int unwrapInt(Value v) {
        if (v instanceof VInt) {
            return ((VInt) v).getValue();
        } else {
            throw new RuntimeException("Runtime type error: Expected an int but got value " + v);
        }
    }

    private String unwrapString(Value v) {
        if (v instanceof VString) {
            return ((VString) v).getValue();
        } else {
            throw new RuntimeException("Runtime type error: Expected a string but got value " + v);
        }
    }

    // Given a value and a type, performs a cast (according to the rules in the spec) if possible,
    // raising a CastException otherwise.
    private Value cast(Value vFrom, Type ty) throws CastException {
        // Cast to Int
        if (ty instanceof TyInt) {
            if (vFrom instanceof VInt) {
                return vFrom; // Int to Int - no change needed
            } else if (vFrom instanceof VBool) {
                // Bool to Int: true → 1, false → 0
                boolean boolVal = ((VBool) vFrom).getValue();
                return new VInt(boolVal ? 1 : 0);
            } else if (vFrom instanceof VString) {
                // String to Int: parse the string as an integer
                String strVal = ((VString) vFrom).getValue();
                try {
                    int intVal = Integer.parseInt(strVal);
                    return new VInt(intVal);
                } catch (NumberFormatException e) {
                    throw new CastException("Cannot cast string \"" + strVal + "\" to Int");
                }
            }
        }
        // Cast to Bool
        else if (ty instanceof TyBool) {
            if (vFrom instanceof VBool) {
                return vFrom; // Bool to Bool - no change needed
            } else if (vFrom instanceof VInt) {
                // Int to Bool: 0 → false, non-zero → true
                int intVal = ((VInt) vFrom).getValue();
                return new VBool(intVal != 0);
            } else if (vFrom instanceof VString) {
                // String to Bool: "true" → true, "false" → false, anything else is an error
                String strVal = ((VString) vFrom).getValue();
                if (strVal.equals("true")) {
                    return new VBool(true);
                } else if (strVal.equals("false")) {
                    return new VBool(false);
                } else {
                    throw new CastException("Cannot cast string \"" + strVal + "\" to Bool");
                }
            }
        }
        // Cast to String
        else if (ty instanceof TyString) {
            if (vFrom instanceof VString) {
                return vFrom; // String to String - no change needed
            } else if (vFrom instanceof VInt) {
                // Int to String: convert to string representation
                int intVal = ((VInt) vFrom).getValue();
                return new VString(Integer.toString(intVal));
            } else if (vFrom instanceof VBool) {
                // Bool to String: "true" or "false"
                boolean boolVal = ((VBool) vFrom).getValue();
                return new VString(Boolean.toString(boolVal));
            }
        }
        // Cast to Unit is not supported
        else if (ty instanceof TyUnit) {
            if (vFrom instanceof VUnit) {
                return vFrom; // Unit to Unit - no change needed
            }
        }
        
        // If we get here, the cast is not supported
        throw new CastException("Cannot cast from " + vFrom + " to " + ty);
    }

    // Given a map from function names to function definitions, and a value environment,
    // return the value resulting from evaluating expression e
    public Value interpExpr(Map<String, FnDef> fnDefs, Environment<Value> valEnv, Expr e) {
        // Handle literals (constants)
        if (e instanceof EInt) {
            return new VInt(((EInt) e).getValue());
        } else if (e instanceof EBool) {
            return new VBool(((EBool) e).getValue());
        } else if (e instanceof EString) {
            return new VString(((EString) e).getValue());
        } else if (e instanceof EUnit) {
            return new VUnit();
        }
        // Handle variable lookup
        else if (e instanceof EVar) {
            String varName = ((EVar) e).getVar();
            return valEnv.lookup(varName);
        }
        // Handle binary operations
        else if (e instanceof EBinOp) {
            EBinOp binOp = (EBinOp) e;
            Value v1 = interpExpr(fnDefs, valEnv, binOp.getE1());
            Value v2 = interpExpr(fnDefs, valEnv, binOp.getE2());
            
            switch (binOp.getOp()) {
                // Arithmetic operations
                case ADD:
                    return new VInt(unwrapInt(v1) + unwrapInt(v2));
                case SUB:
                    return new VInt(unwrapInt(v1) - unwrapInt(v2));
                case MUL:
                    return new VInt(unwrapInt(v1) * unwrapInt(v2));
                case DIV:
                    int divisor = unwrapInt(v2);
                    if (divisor == 0) {
                        throw new RuntimeException("Division by zero");
                    }
                    return new VInt(unwrapInt(v1) / divisor);
                case MOD:
                    int modDivisor = unwrapInt(v2);
                    if (modDivisor == 0) {
                        throw new RuntimeException("Modulo by zero");
                    }
                    return new VInt(unwrapInt(v1) % modDivisor);
                
                // Comparison operations
                case LT:
                    return new VBool(unwrapInt(v1) < unwrapInt(v2));
                case GT:
                    return new VBool(unwrapInt(v1) > unwrapInt(v2));
                case EQ:
                    // For equality, we need to handle different types
                    if (v1 instanceof VInt && v2 instanceof VInt) {
                        return new VBool(unwrapInt(v1) == unwrapInt(v2));
                    } else if (v1 instanceof VBool && v2 instanceof VBool) {
                        return new VBool(unwrapBool(v1) == unwrapBool(v2));
                    } else if (v1 instanceof VString && v2 instanceof VString) {
                        return new VBool(unwrapString(v1).equals(unwrapString(v2)));
                    } else if (v1 instanceof VUnit && v2 instanceof VUnit) {
                        return new VBool(true); // All Unit values are equal
                    } else {
                        return new VBool(false); // Different types are never equal
                    }
                
                // Logical operations
                case AND:
                    return new VBool(unwrapBool(v1) && unwrapBool(v2));
                case OR:
                    return new VBool(unwrapBool(v1) || unwrapBool(v2));
                default:
                    throw new RuntimeException("Unknown binary operator: " + binOp.getOp());
            }
        }
        // Handle NOT operator
        else if (e instanceof ENot) {
            Value v = interpExpr(fnDefs, valEnv, ((ENot) e).getExpr());
            return new VBool(!unwrapBool(v));
        }
        // Handle conditionals (if-then-else)
        else if (e instanceof ECond) {
            ECond cond = (ECond) e;
            Value testVal = interpExpr(fnDefs, valEnv, cond.getTest());
            boolean testBool = unwrapBool(testVal);
            
            if (testBool) {
                return interpExpr(fnDefs, valEnv, cond.getThenBranch());
            } else {
                return interpExpr(fnDefs, valEnv, cond.getElseBranch());
            }
        }
        // Handle let expressions
        else if (e instanceof ELet) {
            ELet let = (ELet) e;
            Value subjectVal = interpExpr(fnDefs, valEnv, let.getSubject());
            Environment<Value> extendedEnv = valEnv.extend(let.getBinder(), subjectVal);
            return interpExpr(fnDefs, extendedEnv, let.getContinuation());
        }
        // Handle function calls
        else if (e instanceof EFnCall) {
            EFnCall fnCall = (EFnCall) e;
            String fnName = fnCall.getFnName();
            
            if (!fnDefs.containsKey(fnName)) {
                throw new RuntimeException("Undefined function: " + fnName);
            }
            
            FnDef fnDef = fnDefs.get(fnName);
            List<Expr> args = fnCall.getArgs();
            List<AnnotatedParam> params = fnDef.getParams();
            
            if (args.size() != params.size()) {
                throw new RuntimeException(
                    String.format("Function %s expects %d arguments but got %d", 
                        fnName, params.size(), args.size()));
            }
            
            // Create a new environment for the function execution
            Environment<Value> fnEnv = new Environment<>();
            
            // Evaluate all arguments and bind them to parameters
            for (int i = 0; i < args.size(); i++) {
                Value argVal = interpExpr(fnDefs, valEnv, args.get(i));
                fnEnv = fnEnv.extend(params.get(i).param, argVal);
            }
            
            // Execute the function body in the new environment
            return interpExpr(fnDefs, fnEnv, fnDef.getBody());
        }
        // Handle print expressions
        else if (e instanceof EPrint) {
            EPrint print = (EPrint) e;
            Value v = interpExpr(fnDefs, valEnv, print.getExpr());
            System.out.println(v);
            return new VUnit(); // print returns Unit
        }
        // Handle getInput
        else if (e instanceof EGetInput) {
            String input = reader.nextLine();
            return new VString(input);
        }
        // Handle type casts
        else if (e instanceof ECast) {
            ECast castExpr = (ECast) e;
            Value v = interpExpr(fnDefs, valEnv, castExpr.getExpr());
            return cast(v, castExpr.getType());
        }
        // Handle string concatenation
        else if (e instanceof EConcat) {
            EConcat concat = (EConcat) e;
            List<Expr> exprs = concat.getExprs();
            StringBuilder sb = new StringBuilder();
            
            for (Expr expr : exprs) {
                Value v = interpExpr(fnDefs, valEnv, expr);
                if (!(v instanceof VString)) {
                    throw new RuntimeException("concat requires String arguments, but got " + v);
                }
                sb.append(unwrapString(v));
            }
            
            return new VString(sb.toString());
        }
        else {
            throw new RuntimeException("Unknown expression type: " + e.getClass().getName());
        }
    }

    // Runs a program by constructing a map from function names to function definitions,
    // and evaluating the main expression under an empty value environment
    public Value interpProgram(Program prog) {
        // Build map of function definitions
        Map<String, FnDef> fnDefs = new HashMap<>();
        for (FnDef def : prog.getFunctionDefs()) {
            String fnName = def.getFnName();
            if (fnDefs.containsKey(fnName)) {
                throw new RuntimeException("Duplicate function definition: " + fnName);
            }
            fnDefs.put(fnName, def);
        }
        
        // Evaluate the main expression with an empty environment
        return interpExpr(fnDefs, new Environment<>(), prog.getMainExpr());
    }
}