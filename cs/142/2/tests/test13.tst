var a : int;
const b = 6;

void p(int &a, short b)
{
 a = b+1;
}

main()
{
get(a,b);

if(a < b)
{
  while(a < b){
   ::p(a, a);
  }
}
else
{
  :p();
}

}