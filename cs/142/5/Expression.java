import java.util.*;

public interface Expression
{

    public SymbolTable.TypeDesignator type (SymbolTable table);
    public boolean referenceable (SymbolTable table);
    public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table);

    interface Designator extends Expression
    {

        public void assignRegisterTo (CodeGen codeGen, int register, SymbolTable table);

        public class Variable implements Designator
        {

            String name;

            Variable (String n)
            {
                name = n;
            }

            public SymbolTable.TypeDesignator type (SymbolTable table)
            {
                SymbolTable.Symbol  symbol = table.getBinding (name, "VAR");
                if (symbol == null) symbol = table.getBinding (name, "CONST");
                if (symbol == null) return null;
                else                return symbol.type ();
            }

            public boolean referenceable (SymbolTable table)
            {
                return table.getBinding (name, "VAR") != null;
            }

            public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table)
            {
                SymbolTable.Symbol symbol = table.getBinding (name, "VAR");
                {
                    if (symbol == null) symbol = table.getBinding (name, "CONST");
                    if (symbol == null) return;
                }
                symbol.loadValueIntoRegister (codeGen, register);
            }

            public void assignRegisterTo (CodeGen codeGen, int register, SymbolTable table)
            {
                SymbolTable.Symbol.SimplyTyped.Variable variable = (SymbolTable.Symbol.SimplyTyped.Variable) table.getBinding (name, "VAR");
                codeGen.storeValue (register, variable.offset);
            }

        }

        public class ArrayReference implements Designator
        {

            Designator baseDesignator;
            Expression index;

            ArrayReference (Designator bd, Expression i)
            {
                baseDesignator = bd;
                index = i;
            }

            public SymbolTable.TypeDesignator type (SymbolTable table)
            {
                SymbolTable.TypeDesignator type = baseDesignator.type (table);
                if (type == null) return null;
                else              return type.dereferencedType ();
            }

            public boolean referenceable (SymbolTable table) { return true; }

            public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table) { System.err.println ("Not implemented!"); System.exit (3); }

            public void assignRegisterTo (CodeGen codeGen, int register, SymbolTable table)
            {
                System.err.println ("assignRegisterTo not implemented!"); System.exit (5);
            }

        }

    }

    public class Number implements Expression
    {
        short value;
        Number (short v) { value = v; }
        public SymbolTable.TypeDesignator type (SymbolTable table) { return SymbolTable.TypeDesignator.SHORT; }
        public boolean referenceable (SymbolTable table) { return false; }
        public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table) { codeGen.loadConstant (register, value); }
    }

    public class ProcedureCall implements Expression
    {

        String name;
        List <Expression.Designator> arguments;

        ProcedureCall (String n, List <Expression.Designator> a)
        {
            name = n;
            arguments = a;
        }

        public SymbolTable.TypeDesignator type (SymbolTable table)
        {
            SymbolTable.Symbol symbol = table.getBinding (name, "PROCEDURE");
            if (symbol == null) return null;
            else                return symbol.type ();
        }

        public boolean referenceable (SymbolTable table) { return false; }

        public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table) { System.err.println ("Not implemented!"); System.exit (3); }

    }

    abstract class BinaryOperation implements Expression
    {

        Expression expression0, expression1;

        BinaryOperation (Expression e0, Expression e1)
        {
            expression0 = e0;
            expression1 = e1;
        }

        abstract void combineRegisters (CodeGen codeGen, int register0, int register1);

        public SymbolTable.TypeDesignator type (SymbolTable table)
        {
            return SymbolTable.TypeDesignator.Combine.symmetrically (expression0.type (table), expression1.type (table));
        }

        public static class Addition       extends BinaryOperation
        {
            Addition       (Expression e0, Expression e1) { super (e0, e1); }
            void combineRegisters (CodeGen codeGen, int register0, int register1) { codeGen.add      (register0, register0, register1); }
        }

        public static class Subtraction    extends BinaryOperation
        {
            Subtraction    (Expression e0, Expression e1) { super (e0, e1); }
            void combineRegisters (CodeGen codeGen, int register0, int register1) { codeGen.subtract (register0, register0, register1); }
        }

        public static class Multiplication extends BinaryOperation
        {
            Multiplication (Expression e0, Expression e1) { super (e0, e1); }
            void combineRegisters (CodeGen codeGen, int register0, int register1) { codeGen.multiply (register0, register0, register1); }
        }

        public static class Division       extends BinaryOperation
        {
            Division       (Expression e0, Expression e1) { super (e0, e1); }
            void combineRegisters (CodeGen codeGen, int register0, int register1) { codeGen.divide   (register0, register0, register1); }
        }

        public boolean referenceable (SymbolTable table) { return false; }

        public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table)
        {
            expression0.evaluateIntoRegister (codeGen, register, table);
            int tmpRegister = codeGen.getTemporaryRegister ();
            expression1.evaluateIntoRegister (codeGen, tmpRegister, table);
            combineRegisters (codeGen, register, tmpRegister);
            codeGen.releaseTemporaryRegister (tmpRegister);
        }

    }

}
