struct account {
    double __attribute__((warning("3.0, 4.0"))) account_number;
   double *first_name;
   double *last_name;
   double balance;
};

int main()
{
        struct account s;
        s.account_number = 3;
        return 0;
}
