DIR=$(dir $(realpath $(firstword $(MAKEFILE_LIST))))

default: parser runtime boogie exe

all: parser runtime boogie exe refman

exe: parser
	(cd ${DIR} ; msbuild Source/Dafny.sln )

boogie: ${DIR}/../boogie/Binaries/Boogie.exe

${DIR}/../boogie/Binaries/Boogie.exe:
	(cd ${DIR}/../boogie ; msbuild Source/Boogie.sln )

parser: 
	make -C ${DIR}/Source/Dafny -f Makefile.linux all

runtime: ${DIR}/Binaries/DafnyRuntime.jar

${DIR}/Binaries/DafnyRuntime.jar:
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew copyJarToBinaries)

refman:
	make -C ${DIR}/docs/DafnyReferenceManual

z3-mac:
	wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-osx-10.14.1.zip
	unzip z3-4.8.4.d6df51951f4c-x64-osx-10.14.1.zip
	mv z3-4.8.4.d6df51951f4c-x64-osx-10.14.1 dafny/Binaries/z3

clean:
	(cd ${DIR} ; msbuild Source/Dafny.sln -target:clean )
	make -C ${DIR}/Source/Dafny -f Makefile.Linux clean
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew clean)
	make -C ${DIR}/docs/DafnyReferenceManual clean
