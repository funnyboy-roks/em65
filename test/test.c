int main(void)
{
    char *s = "hello world\n";

    char c = 0;

    for(; s[c] != '\0'; ++c) {
        *((char *)0x2000) = s[c];
    }

}
