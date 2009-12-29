public interface Statement
{

    public void execute (CodeGen codeGen, SymbolTable table);


    public class Dummy implements Statement
    {
        public void execute (CodeGen codeGen, SymbolTable table) { } ;
    }

    public class Assignment implements Statement
    {

        Expression.Designator designator;
        Expression expression;

        public Assignment (Expression.Designator d, Expression e)
        {
            designator = d;
            expression = e;
        }

        public void execute (CodeGen codeGen, SymbolTable table)
        {
            int register = codeGen.getTemporaryRegister ();
            expression.evaluateIntoRegister (codeGen, register, table);
            designator.assignRegisterTo (codeGen, register, table);
            codeGen.releaseTemporaryRegister (register);
        }

    }

    public class StandaloneExpression implements Statement
    {

        Expression expression;

        public StandaloneExpression (Expression e)
        {
            expression = e;
        }

        public void execute (CodeGen codeGen, SymbolTable table)
        {
            expression.evaluateStandalone (codeGen, table);
        }

    }

}
