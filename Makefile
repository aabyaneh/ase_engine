
EFLAGS := -w -g -O3 -m64

CFLAGS := -w -g -O3 -m64 -D'main(a,b)=main(int argc, char** argv)'

ase: ase.cpp engine.cpp mit_bvt_engine.cpp mit_box_bvt_engine.cpp mit_box_abvt_engine.cpp bvt_engine.cpp
	$(CXX) $(EFLAGS) $^ -o $@ -lboolector -lbtor2parser -llgl

selfie: compiler/selfie.c
	$(CC) $(CFLAGS) $^ -o $@