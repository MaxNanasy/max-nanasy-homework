public interface Either <A, B>
{
    public <R> R either (Function <A, R> f0, Function <B, R> f1);
    public class Left <A, B> implements Either <A, B>
    {
        private A d0;
        public Left (A x0)
        {
            d0 = x0;
        }
        public <R> R either (Function <A, R> f0, Function <B, R> f1)
        {
            return f0.apply (d0);
        }
    }
    public class Right <A, B> implements Either <A, B>
    {
        private B d0;
        public Right (B x0)
        {
            d0 = x0;
        }
        public <R> R either (Function <A, R> f0, Function <B, R> f1)
        {
            return f1.apply (d0);
        }
    }
}
