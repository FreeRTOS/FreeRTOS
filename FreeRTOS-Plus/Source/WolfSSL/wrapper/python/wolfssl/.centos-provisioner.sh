[ "$(whoami)" != "root" ] && echo "Sorry, you are not root." && exit 1

rpm -ivh http://dl.fedoraproject.org/pub/epel/epel-release-latest-7.noarch.rpm

yum install -y \
    git autoconf libtool libffi-devel python-devel python34-devel python2-pip

pip install -U pip setuptools

git clone --depth 1 https://github.com/wolfssl/wolfssl.git
[ $? -ne 0 ] && echo "\n\nCouldn't download wolfssl.\n\n" && exit 1

pushd wolfssl

./autogen.sh
./configure
make
make install
echo /usr/local/lib > wolfssl.conf
mv wolfssl.conf /etc/ld.so.conf
ldconfig

popd

rm -rf wolfssl

pushd /vagrant

pip install -r requirements-testing.txt

make clean

tox -epy27,py34 -- -v

popd

# pip install wolfssl
# [ $? -ne 0 ] && echo "\n\nCouldn't install wolfssl.\n\n" && exit 1
