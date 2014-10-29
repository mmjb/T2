int send_command()
{
    int x;
    return x;
}

int main( char *  Controller, char DeviceId)
{
    const int maxRetries = 4;
    int retryCount = 0;
    int selected   = 0;
    while( !selected & retryCount < maxRetries ) {
        selected = send_command();
        ++retryCount;
    }
    return selected;
}
