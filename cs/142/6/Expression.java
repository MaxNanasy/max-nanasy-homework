import java.util.*;

public abstract class Expression
{

    abstract public SymbolTable.TypeDesignator type (SymbolTable table);
    abstract public boolean referenceable (SymbolTable table);
    abstract public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table);

    public void evaluateStandalone (CodeGen codeGen, SymbolTable table)
    {
        int tempRegister = codeGen.getTemporaryRegister ();
        evaluateIntoRegister (codeGen, tempRegister, table);
        codeGen.releaseTemporaryRegister (tempRegister);
    }

    abstract static class Designator extends Expression
    {

        public void assignRegisterTo (CodeGen codeGen, int register, SymbolTable table)
        {
            int addressRegister = codeGen.getTemporaryRegister ();
            loadAddressIntoRegister (codeGen, addressRegister, table);
            codeGen.storeValueIndirectly (register, addressRegister);
            codeGen.releaseTemporaryRegister (addressRegister);
        }

        abstract protected void loadAddressIntoRegister (CodeGen codeGen, int register, SymbolTable table);

        public static class Variable extends Designator
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
                if (variable.register)
                    codeGen.storeArgument (register, variable.offset);
                else
                    codeGen.storeValue (register, variable.offset);
            }

            protected void loadAddressIntoRegister (CodeGen codeGen, int register, SymbolTable table)
            {
                codeGen.globalAddressToRegister (register, ((SymbolTable.Symbol.SimplyTyped.Variable) table.getBinding (name, "VAR")).offset);
            }

            /*
            public void assignRegisterTo (CodeGen codeGen, int register, SymbolTable table)
            {
                SymbolTable.Symbol.SimplyTyped.Variable variable = (SymbolTable.Symbol.SimplyTyped.Variable) table.getBinding (name, "VAR");
                codeGen.storeValue (register, variable.offset);
            }
            */

        }

        public static class ArrayReference extends Designator
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

            public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table)
            {
                int addressRegister = codeGen.getTemporaryRegister ();
                loadAddressIntoRegister (codeGen, addressRegister, table);
                codeGen.loadValueIndirectly (register, addressRegister);
                codeGen.releaseTemporaryRegister (addressRegister);
            }

            protected void loadAddressIntoRegister (CodeGen codeGen, int register, SymbolTable table)
            {
                codeGen.comment ("BEGIN Load array address into register $t" + register);
                int indexRegister = codeGen.getTemporaryRegister ();
                index.evaluateIntoRegister (codeGen, indexRegister, table);
                codeGen.constMultiply (indexRegister, indexRegister, 4);
                baseDesignator.loadAddressIntoRegister (codeGen, register, table);
                codeGen.add (register, register, indexRegister);
                codeGen.releaseTemporaryRegister (indexRegister);
                codeGen.comment ("END   Load array address into register $t" + register);
            }

        }

    }

    public static class Number extends Expression
    {
        short value;
        Number (short v) { value = v; }
        public SymbolTable.TypeDesignator type (SymbolTable table) { return SymbolTable.TypeDesignator.SHORT; }
        public boolean referenceable (SymbolTable table) { return false; }
        public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table) { codeGen.loadConstant (register, value); }
    }

    public static class ProcedureCall extends Expression
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

        public void evaluateIntoRegister (CodeGen codeGen, int register, SymbolTable table)
        {
            codeGen.comment ("BEGIN procedure call");
            codeGen.pushReturnAddress ();
            codeGen.pushTemporaryRegisters ();
            SymbolTable.Symbol.SimplyTyped.Procedure procedure = (SymbolTable.Symbol.SimplyTyped.Procedure) table.getBinding (name, "PROCEDURE");
            int tempRegister = codeGen.getTemporaryRegister ();
            for (int i = 0; i < arguments.size (); ++ i) {
                String name = procedure.table.get (i).key;
                arguments.get (i).evaluateIntoRegister (codeGen, tempRegister, table);
                new Designator.Variable (name).assignRegisterTo (codeGen, tempRegister, procedure.table);
                codeGen.releaseTemporaryRegister (tempRegister);
            }                
            codeGen.jumpAndLink (procedure.label);
            codeGen.popTemporaryRegisters ();
            codeGen.popReturnAddress ();
            codeGen.loadReturnValue (register);
            codeGen.comment ("END   procedure call");
        }

    }

    abstract static class BinaryOperation extends Expression
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
