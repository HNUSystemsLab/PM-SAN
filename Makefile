

noname:
	clang++ `llvm-config --cxxflags` -fno-rtti -fPIC -shared llvm_secondpass.cpp -o llvmhello.so `llvm-config --ldflags`

floatinit:
	clang++ -fPIC -shared -o libfloat.so floatzone_handler.cpp -ldl
#if run with flaotinit, add LD_PRELOAD="./libfloat.so" before ./program

doublefreee:
	clang++ double_free_ntx.cpp -Wl,-rpath=/home/cwk/cwk/noname/llvm_try -L./ -I./ -lpmem -lpmemobj -lfloatzone -o output

clean:
	rm -rf *.so *.o *.ll *.pch *.gch *.s

