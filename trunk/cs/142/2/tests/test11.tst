var a, b : int;
main()
{
  get(a,b);
  while(a != b)
  {
    if( a < b )
    {
      b = b - a;
     }
    else
    {
      a = a - b;
    }
  }

  print(a)  
}