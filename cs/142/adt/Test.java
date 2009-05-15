public class Test
{
    private static <A, B> String eitherToString (Either <A, B> e)
    {
        return e.either ( new Function <A, String> () { public String apply (A x) { return "Left "  + x; } }
                        , new Function <B, String> () { public String apply (B x) { return "Right " + x; } }
                        );
    }
    public static void main (String argv [])
    {
        System.out.println (eitherToString (new Either.Left  <Boolean, Integer> (false)));
        System.out.println (eitherToString (new Either.Right <Boolean, Integer> (20000)));
    }
}
