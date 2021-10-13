#!/bin/sh

id=`docker create gidonernst/legion-symcc`
echo $id
docker cp $id:/root/lib ubuntu2004
docker cp $id:/root/lib32 ubuntu2004
docker rm $id