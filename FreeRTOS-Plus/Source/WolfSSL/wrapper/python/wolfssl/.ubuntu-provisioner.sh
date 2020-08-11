[ "$(whoami)" != "root" ] && echo "Sorry, you are not root." && exit 1

apt-get update

apt-get install -y \
    git autoconf libtool python-dev python3-dev python-pip libffi-dev

pip install -U pip setuptools

git clone --depth 1 https://github.com/wolfssl/wolfssl.git
[ $? -ne 0 ] && echo "\n\nCouldn't download wolfssl.\n\n" && exit 1

pushd wolfssl

./autogen.sh
./configure
make
make install
ldconfig

popd

rm -rf wolfssl

pushd /vagrant

pip install -r requirements-testing.txt

make clean

tox -epy27,py34 -- -v

popd

# pip install wolfssl
# [ $? -ne 0 ] && echo -e "\n\nCouldn't install wolfssl.\n\n" && exit 1
