This is a howto file describing the installation of ITAP and ITCP from scratch on Linux systems without
using root priviledges. ITAP and ITCP together make the Computer Assisted Theorem Provers for Information Theory (catpit) suit. We assume that you have a working internet
connection for the 'wget' commands below that fetch the required tarballs from the
web. If you wish to install only one of ITAP or ITCP you can jump over the steps that
are indicated to be specific to one of them.
## Step 1. Create the catpit folder (common)
```{r, engine='bash', count_lines}
mkdir catpit
cd catpit
mkdir lib include
```
## Step 2. Install GMP (common)
###Get GMP

```{r, engine='bash', count_lines}
wget https://gmplib.org/download/gmp/gmp-6.1.0.tar.xz
tar -xf gmp-6.1.0.tar.xz
```
### Install GMP locally
```{r, engine='bash', count_lines}
mkdir gmp_install
cd gmp-6.1.0
./configure --prefix=$PWD/../gmp_install
```

#### Use the -j switch with ```make``` below, and in the rest of this howto if you are certain you know what you are doing, otherwise don't bother about it.  
```{r, engine='bash', count_lines}
make
make install
make check
cd ../
cp gmp_install/lib/* lib/
cp gmp_install/include/* include/
rm -rf gmp-6.1.0
```
## Step 2: Install GAP (common)
```{r, engine='bash', count_lines}
wget http://www.gap-system.org/pub/gap/gap48/tar.gz/gap4r8p4_2016_06_04-12_41.tar.gz
tar -xf gap*.tar.gz
cd gap4r8
./configure  --with-gmp=$PWD/../gmp_install
make
```
## Step 3: Install Singular (ITAP specific)
### This step follows instructions at https://www.singular.uni-kl.de/index.php/singular-download/109.html, to obtain pre-compiled binaries of Singular for linux systems.

#### In the first line below, replace x86_64-Linux appropriately based on your computer architecture (make sure you have the correct name of the latest archive by navigating to [http://www.mathematik.uni-kl.de/ftp/pub/Math/Singular/UNIX/](http://www.mathematik.uni-kl.de/ftp/pub/Math/Singular/UNIX/) in your web browser, where the latest archives are hosted). 
```{r, engine='bash', count_lines}
mkdir singular_install; cd singular_install
wget http://www.mathematik.uni-kl.de/ftp/pub/Math/Singular/UNIX/Singular-4.1.0-x86_64-Linux.tar.gz
tar -xf Singular-4.1.0-x86_64-Linux.tar.gz
cd ../
```
#### Copy paste the following line in the file "$HOME/.bashrc", after substituting path-to-singular-bin with the absolute path to the ```bin``` directory created inside ```singular_install``` directory, as a result of the most recent ```tar``` command.
```{r, engine='bash', count_lines}
export PATH=path-to-singular-bin/:$PATH
```
#### Create the .bashrc file if it doesn't exist already. This gives you the permanent ability to type "Singular" in the terminal to invoke the Singular's terminal based interface. While we wont be using this interface, it is convenient at a later time (Step 5) for setting the "sing_exec" variable in the GAP-Singular interface, that directs ITAP to the Singular executable.

Note:  The functionality provided by ~/.bashrc is itself dependent on the ~/.profile file, so in case you run into any errors later, make sure these two files are set up correctly. You may want to consult [this stackoverflow answer](http://askubuntu.com/questions/161249/bashrc-not-executed-when-opening-new-terminal)  if you are on Ubuntu.

## Step 4: Download and Install ITAP (ITAP specific)
#### Go to the gap pkg directory
```{r, engine='bash', count_lines}
cd pkg
```
#### If you have git installed:
```{r, engine='bash', count_lines}
git clone https://github.com/jayant91089/itap.git
```
#### Else
```{r, engine='bash', count_lines}
wget https://github.com/jayant91089/itap/archive/master.zip
unzip itap-master.zip
mv -r itap-master itap
```
#### Finally,
```{r, engine='bash', count_lines}
cd ../../
```
## Step 5: End of ITAP installation (ITAP specific)
#### At this point you are ready to use ITAP. To start using ITAP, open a new terminal and navigate to the 'catpit' directory created in Step 0. Then type:
```{r, engine='bash', count_lines}
sh ./gap4r8/bin/gap.sh
```
  # Type the following in the GAP console:
```{r, engine='bash', count_lines}
gap> LoadPackage("ITAP");
gap> sing_exec:="Singular"
```
## Step 6: Get the tarballs needed for ITCP (ITCP specific)

#### Fetch tarballs
```{r, engine='bash', count_lines}
wget http://zlib.net/zlib-1.2.8.tar.gz
wget https://sites.google.com/site/jayantapteshomepage/home/qsopt.tar.gz
wget https://sites.google.com/site/jayantapteshomepage/home/bzip2.tar.gz
tar -xf qsopt.tar.gz
tar -xf bzip2.tar.gz
tar -xf zlib-1.2.8.tar.gz
```
## Step 7: Create appropriate directories for installation (ITCP specific)
```{r, engine='bash', count_lines}
mkdir qsopt_install bzip2_install zlib_install
```

## Step 8: zlib installation (ITCP specific)
```{r, engine='bash', count_lines}
  cd zlib-1.2.8
  ./configure --prefix=$PWD/../zlib_install
  make
  make install
  cd ../
```
## Step 9: bzip2 installation (ITCP specific)
```{r, engine='bash', count_lines}
cd bzip2-1.0.6
make clean
make -f Makefile-libbz2_so
make
make install
if ( test ! -d $PWD/../bzip2_install/lib ) ; then mkdir -p  $PWD/../bzip2_install/lib ; fi
if ( test ! -d $PWD/../bzip2_install/include ) ; then mkdir -p  $PWD/../bzip2_install/include ; fi
cp libbz2.so.1.0.6 $PWD/../bzip2_install/lib/
cp *.h $PWD/../bzip2_install/include/
cd ../
```
## Step 10: Copy headers needed by qsopt_ex to catpit/include directory (ITCP specific)
```{r, engine='bash', count_lines}
cp gmp_install/include/* include/
cp zlib_install/include/* include/
cp bzip2_install/include/* include/
```
#### Now ensure qsopt_ex knows where to look. Substitute the absolute path to the include directory below:
```{r, engine='bash', count_lines}
export C_INCLUDE_PATH=absolute-path-to-catpit/include-directory
```

## Step 11: qsopt_ex installation (ITCP specific)
#### Create the build directory
```{r, engine='bash', count_lines}
cd qsopt-ex-2.5.10.3
mkdir build && cd build
../configure --prefix=$PWD/../../qsopt_install LDFLAGS="-L$PWD/../../gmp_install/lib -L$PWD/../../zlib_install/lib -L$PWD/../../bzip2_install/lib"
make
make install
cd ../../
```
#### Copy qsopt_ex headers and libraries to include and lib folders
```{r, engine='bash', count_lines}
cp qsopt_install/include/qsopt_ex/* include/
cp qsopt_install/lib/* lib/
```
## Step 12: Get qsopt_ex-interface and compile the interface (ITCP specific)
#### Go to the pkg directory of GAP
```{r, engine='bash', count_lines}
cd gap4r8/pkg
```
#### If you have git installed:
```{r, engine='bash', count_lines}
git clone https://github.com/jayant91089/qsopt_ex-interface.git
```
#### Else
```{r, engine='bash', count_lines}
wget https://github.com/jayant91089/qsopt_ex-interface/archive/master.zip
unzip master.zip
mv -r qsopt_ex-interface-master qsopt_ex-interface
```
#### Finally,
```{r, engine='bash', count_lines}
cd qsopt_ex-interface
make all
cd ../../
```
#### This creates an executable named ```qsi``` which acts as the interface between GAP and qsopt_ex

## Step 13: Set-up qsopt_ex-interface (ITCP specific)
#### Open the ```gap/qsinterface.gi``` file inside qsopt_ex-interface directory and define a variable ```qs_exec``` to store the absolute path to the ```qsi``` executable created in the previous step. e.g.
```{r, engine='bash', count_lines}
qs_exec:="/home/jayant/catpit/gap4r8/pkg/qsopt_ex-interface/qsi";
```
#### Paste the following line in the ```$HOME/.bashrc``` (see step 3 for more details about this file), after substituting
```path-to-catpit``` with an appropriate path.
```{r, engine='bash', count_lines}
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:path-to-catpit/lib
```

## Step 14: Get symchm
#### Navigate to ```...catpit/gap4r8/pkg``` directory again and do the following.
#### If you have git installed:
```{r, engine='bash', count_lines}
git clone https://github.com/jayant91089/symchm.git
```
#### Else
```{r, engine='bash', count_lines}
wget https://github.com/jayant91089/symchm/archive/master.zip
unzip symchm-master.zip
mv -r symchm-master symchm
```

## Step 15:  Get ITCP (ITCP specific)
#### Navigate to ```...catpit/gap4r8/pkg``` directory again and do the following.
#### If you have git installed:
```{r, engine='bash', count_lines}
git clone https://github.com/jayant91089/itcp.git
```
#### Else
```{r, engine='bash', count_lines}
wget https://github.com/jayant91089/itcp/archive/master.zip
unzip itcp-master.zip
mv -r itcp-master itcp
```

## Step 16: Test ITCP

#### open a new terminal and navigate to the 'catpit' directory created in Step 0. Then type:
```{r, engine='bash', count_lines}
sh ./gap4r8/bin/gap.sh
```
#### In the gap console type
```{r, engine='bash', count_lines}
gap> LoadPackage("itcp");
```
