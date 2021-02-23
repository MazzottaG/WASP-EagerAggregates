WASP_DIR=$4
gringo --output=smodels $1 $3 | ./wasp.bin --interpreter=cpp_eager --script-directory=. --plugins-file=$2 --stats=2
