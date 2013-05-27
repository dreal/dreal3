# 1 "test4.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "test4.c"
struct account {
   int account_number;
   char *first_name;
   char *last_name;
   float balance;
};

int main()
{
 struct account s;
 s.account_number = 3;
 return 0;
}
