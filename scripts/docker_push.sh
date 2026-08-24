# This script attempts to build all the docker images, and then push then to the repository.
# You'll need to have run `docker login` already;
# check with Mathlib maintainers on Zulip for credentials.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DATE=$(date +"%Y-%m-%d")

cd $DIR && \
./docker_build.sh && \
docker push leanprovercommunity/lean4:$DATE && \
docker push leanprovercommunity/lean4:latest && \
docker push leanprovercommunity/gitpod4:$DATE && \
docker push leanprovercommunity/gitpod4:latest && \
docker push leanprovercommunity/gitpod4-blueprint:$DATE && \
docker push leanprovercommunity/gitpod4-blueprint:latest
