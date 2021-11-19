
CFLAGS := -w -O3 -m64 -D'main(a,b)=main(int argc, char** argv)'

EFLAGS := -w -O3 -m64 -std=c++11 -I./boolector/src/ -I./boolector/deps/cadical/src/ -L./boolector/build/lib/ -L./boolector/deps/cadical/build/ -L./boolector/deps/btor2tools/build/

ase: src/ase.cpp src/engine.cpp src/bvt_engine.cpp src/pvi_bvt_engine.cpp src/pvi_ubox_bvt_engine.cpp
	$(CXX) $(EFLAGS) $^ -o $@ -lboolector -lbtor2parser -lcadical -lpthread

selfie: compiler/selfie.c
	$(CC) $(CFLAGS) $^ -o $@

all: ase selfie