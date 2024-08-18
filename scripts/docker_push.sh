# This script attempts to build all the docker images, and then push then to the repository.
# You'll need to have run `docker login` already;
# check with scott.morrison@gmail.com for credentials.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

cd $DIR && \
./docker_build.sh && \
docker push leanprovercommunity/lean:latest && \
docker push leanprovercommunity/lean:debian && \
docker push leanprovercommunity/mathlib:latest && \
docker push leanprovercommunity/mathlib:debian && \
docker push leanprovercommunity/mathlib:gitpod
