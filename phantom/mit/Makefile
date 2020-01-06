# Compiler flags
CFLAGS := -w -g -O3 -m64 -D'main(a,b)=main(int argc, char** argv)'

# Compile selfie.c into selfie executable
phantom: phantom.c sase.c msiiad.c
	$(CXX) $(CFLAGS) $^ -o $@ -lboolector -lbtor2parser -llgl