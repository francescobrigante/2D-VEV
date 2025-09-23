# simple docker training script
# docker build -t maze-rl .
set -euo pipefail

echo "========Starting RL training\n"

DATASET_FILE="verified_environments.json"
# DATASET_FILE="random_environments.json"   # use this for unverified training
echo "Dataset: ${DATASET_FILE}"

# check if docker is running
if ! /usr/local/bin/docker info > /dev/null 2>&1; then
    echo "Docker is not running."
    exit 1
fi

# check if dataset exists
if [ ! -f "${DATASET_FILE}" ]; then
    echo "ERROR: ${DATASET_FILE} not found. generate dataset first:"
    echo "python dataset_manager.py -n 20 -o ${DATASET_FILE}"
    exit 1
fi

# create models directory if it doesn't exist
mkdir -p models logs

# build docker image
echo "- Building docker image..."
/usr/local/bin/docker build -t maze-rl .

if [ $? -ne 0 ]; then
    echo "Docker build failed"
    exit 1
fi

# run training
echo "===>Starting training..."
docker run --rm \
  -v "$(pwd):/app" \
  -e OMP_NUM_THREADS=1 \
  -e MKL_NUM_THREADS=1 \
  -e MPLBACKEND=Agg \
  maze-rl python /app/train_rl_agent.py --dataset "/app/${DATASET_FILE}"

if [ $? -eq 0 ]; then
    echo "\n==========Training completed! check ./models/ for saved models"
else
    echo "ERROR: training failed"
fi