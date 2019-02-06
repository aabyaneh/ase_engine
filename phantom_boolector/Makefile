# Compiler flags
CFLAGS := -w -O3 -m64 -D'main(a,b)=main(int argc, char** argv)' -I ../boolector_/src/

# Compile selfie.c into selfie executable
phantom: phantom.c sase.c
	$(CC) $(CFLAGS) $^ -o $@ -lboolector -lbtor2parser -llgl