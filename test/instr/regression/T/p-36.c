
int InterfaceType;
int Dc;
void * fdoExtension;
int ntStatus;
int MaximumInterfaceType;

void foo() {}

main()
{
        while(InterfaceType < MaximumInterfaceType) {




            InterfaceType++ ;

            ntStatus = nondet();

            if (ntStatus>0 && (ntStatus != 256)) {

                return ntStatus;
            }

        }

}
