int Index;
int Retries;
int Status;

int SPStallExecution(int x) {}
int SPReadPortUchar() { int x; return x;}
void SPWritePortUchar() {}

main()
{
    do {
        SPWritePortUchar();

        for (Index = 0; Index < 500000; Index++) {

            if (SPReadPortUchar()) {

                SPWritePortUchar();

                if (!(SPReadPortUchar())) {
                    return Status;
                }
            }
            SPStallExecution(1);
        }
    } while (Retries++ < 10);
}
