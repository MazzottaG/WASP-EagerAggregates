WASP_DIR=$4
gringo --output=smodels $1 $3 | ./wasp.bin --interpreter=cpp_eager --script-directory=. --plugins-file=$2 --min-conflict=500 --min-heap-size=100 --max-heap-size=500
