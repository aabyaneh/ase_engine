# Compiler flags
CFLAGS := -w -O3 -m64 -D'main(a,b)=main(int argc, char** argv)' -Iboolector/src/ -Lboolector/build/lib/ -Lboolector/deps/lingeling/ -Lboolector/deps/btor2tools/build/

# Compile selfie.c into selfie executable
phantom: phantom.c sase.c
	$(CC) $(CFLAGS) $^ -o $@ -lboolector -lbtor2parser -llgl