FROM ubuntu:latest

ENV TOP=/opt
WORKDIR $TOP

RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       cmake \
       g++ \
       gcc \
       git \
       libc-dev \
       make \
       wget \
       curl \
  && rm -rf /var/lib/apt/lists/*

RUN g++ --version
RUN git clone https://github.com/Boolector/boolector

RUN cd boolector \
  && git checkout 4999474f4e717c206577fd2b1549bd4a9f4a36e7 \
  && ./contrib/setup-cadical.sh \
  && ./contrib/setup-btor2tools.sh \
  && ./configure.sh --only-cadical  \
  && cd build \
  && make \
  && make install

RUN cd $TOP \
  && git clone https://github.com/aabyaneh/ase_engine \
  && cd ase_engine \
  && make selfie

RUN cd ase_engine \
  && g++ -w -g -O3 -m64 -std=c++11 -I../boolector/src/ -I../boolector/deps/cadical/src/ -L../boolector/build/lib/ -L../boolector/deps/cadical/build/ -L../boolector/deps/btor2tools/build/ ase.cpp engine.cpp bvt_engine.cpp mit_bvt_engine.cpp mit_box_bvt_engine.cpp -o ase -lboolector -lbtor2parser -lcadical -lpthread