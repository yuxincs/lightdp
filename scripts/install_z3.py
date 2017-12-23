import json
import sys
import os
import wget
import zipfile
import shutil
from functools import reduce
try:
    import urllib.request as urlrequest
except ImportError:
    import urllib as urlrequest


def main():
    releases = json.loads(urlrequest.urlopen('https://api.github.com/repos/Z3Prover/z3/releases').read())[0]
    system = sys.platform
    library_files = ['.txt', '.py']
    if 'linux' in system:
        system = 'ubuntu-14.04'
        library_files.append('libz3.a')
    elif 'darwin' in system:
        system = 'osx'
        library_files.append('libz3.dylib')
    elif 'windows' in system:
        system = 'win'
        library_files.append('Microsoft.Z3.dll')
        library_files.append('Microsoft.Z3.xml')

    print('Downloading %s...' % releases['name'])

    for asset in releases['assets']:
        if system in asset['name'] and 'x64' in asset['name']:
            # download the release zip file
            os.mkdir('./tmp')
            os.mkdir('./z3')
            wget.download(asset['browser_download_url'], out='./tmp/z3.zip')
            print('Download finished. Extracting files...')
            zf = zipfile.ZipFile('./tmp/z3.zip')
            zf.extractall('./tmp')

            for file in zf.namelist():
                # move the license file, python bindings and corresponding library
                for library_file in library_files:
                    if file.endswith(library_file):
                        shutil.move('./tmp/' + file, './z3/' + file[file.rfind('/'):])

            print('Extract finished, removing temporary files...')
            shutil.move('./z3', '../')
            shutil.rmtree('./tmp')
            print('Done.')


if __name__ == '__main__':
    main()