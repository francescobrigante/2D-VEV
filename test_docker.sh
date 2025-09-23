# docker testing script

MODEL_PATH=$1

echo "testing model: $MODEL_PATH"

# check if model exists
if [ ! -f "$MODEL_PATH.zip" ]; then
    echo "ERROR model not found: $MODEL_PATH.zip"
    echo "available models:"
    ls -la models/ 2>/dev/null || echo "no models found"
    exit 1
fi


# build docker image
echo "- Building docker image..."
/usr/local/bin/docker build -t maze-rl .

if [ $? -ne 0 ]; then
    echo "Docker build failed"
    exit 1
fi

# run testing
echo "\n=========Running test..."
docker run --rm \
    -v "$(pwd)/models:/app/models" \
    -v "$(pwd)/test_set.json:/app/test_set.json" \
    -e OMP_NUM_THREADS=1 \
    -e MKL_NUM_THREADS=1 \
    maze-rl python test_rl_agent.py --model $MODEL_PATH --dataset test_set.json --stochastic