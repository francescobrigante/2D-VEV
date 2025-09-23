# usage: ./run.sh file.pml ltl_property

if [ $# -ne 2 ]; then
    echo "Usage: $0 <file.pml> <ltl_property>"
    exit 1
fi

PML_FILE=$1
LTL_PROP=$2

spin -a "$PML_FILE"

gcc -o pan pan.c -DVECTORSZ=5000

./pan -N "$LTL_PROP" -m100000
