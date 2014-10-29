int Index;
int Retries;
int Status;

main()
{
    do {
        //SPWritePortUchar();

        for (Index = 0; Index < 500000; Index++) {

            if (nondet()) {

                //SPWritePortUchar();

                if (!(nondet())) {
                    return Status;
                }
            }
            //SPStallExecution(1);
        }
    } while (Retries < 10);
}
