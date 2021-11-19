# How to install the ASE engine
In this section we explain how to install the ASE engine.

**IMPORTANT**. Please make sure that the machine on which the installation is done has enough resources (at least 8 GB of RAM, and 2 CPU cores). Since we measure execution times please make sure that there is sufficient resources while executing the experiments.

## Install on a Linux machine:
Execute the following commands in a terminal:
```
1. sudo apt-get update ;
2. sudo apt-get install -y --no-install-recommends \
       ca-certificates \
       cmake \
       g++ \
       gcc \
       git \
       libc-dev \
       make \
       wget \
       curl ;

```
Go to the root directory and then:
```
3. git clone https://github.com/Boolector/boolector ;
4. cd boolector \
  && git checkout 4999474f4e717c206577fd2b1549bd4a9f4a36e7 \
  && ./contrib/setup-cadical.sh \
  && ./contrib/setup-btor2tools.sh \
  && ./configure.sh --only-cadical  \
  && cd build \
  && make ;

5. cd .. ; cd .. ;
6. make all;
```
Now you should see `ase`, `parti`, and `selfie` executables.

## Install on docker:
In this section we explain how to run the ASE engine on using docker.

**IMPORTANT**. You need to install the engine natively on a real machine to produce accurate execution time measurements. Otherwise, the generated execution times will not be accurate.

### Install on docker (by building docker image locally)
1. download and install docker on your machine
2. run docker
3. **IMPORTANT:** go to docker settings, and then in "Resources" tab: increase the **"Memory"** to at least **'8 GB'** and "CPUs" to 2
4. go to the root directory where "Dockerfile" is located
5. open a terminal
6. execute the following command: `docker build --tag ase .`
7. then execute the following command: `docker run -it ase`

In the root folder you should see `ase`, `parti`, and `selfie` executables.