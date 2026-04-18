DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DATE=$(date +"%Y-%m-%d")

cd $DIR/../.docker/lean && \
docker build -t leanprovercommunity/lean4:$DATE -t leanprovercommunity/lean4:latest . && \
cd $DIR/../.docker/gitpod && \
docker build -t leanprovercommunity/gitpod4:$DATE -t leanprovercommunity/gitpod4:latest . && \
cd $DIR/../.docker/gitpod-blueprint && \
docker build -t leanprovercommunity/gitpod4-blueprint:$DATE -t leanprovercommunity/gitpod4-blueprint:latest .
