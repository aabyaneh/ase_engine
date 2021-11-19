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

RUN cd $TOP \
  && git clone https://github.com/aabyaneh/ase_artifact

RUN cd ase_artifact \
  && git clone https://github.com/Boolector/boolector

RUN cd ase_artifact \
  && cd boolector \
  && git checkout 4999474f4e717c206577fd2b1549bd4a9f4a36e7 \
  && ./contrib/setup-cadical.sh \
  && ./contrib/setup-btor2tools.sh \
  && ./configure.sh --only-cadical  \
  && cd build \
  && make \
  && make install

RUN cd $TOP \
  && cd ase_artifact \
  && make all