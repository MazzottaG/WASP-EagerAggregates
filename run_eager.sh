WASP_DIR=$4
gringo --output=smodels $1 $3 | ./$WASP_DIR/wasp.bin --interpreter=cpp_eager --script-directory=. --plugins-file=$2 -n 0 --trace-solver=10 --trace-learning=10
