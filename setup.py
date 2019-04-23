from setuptools import setup, find_packages

# Get the long description from the relevant file
with open('README.md') as f:
    long_description = f.read()

setup(
    name='lightdp',
    version='0.1',
    description='LightDP - A Light-Weight Imperative Language That Provides Differential Privacy Proofs.',
    long_description=long_description,
    url='',
    author='Danfeng Zhang/Daniel Kifer/Yuin Wang/Ding Ding',
    author_email='{dkifer,zhang,yxwang}@psu.edu,dingsquared@gmail.com',
    license='MIT',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Developers',
        'Topic :: Programming Language :: Differential Privacy',
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.4',
        'Programming Language :: Python :: 3.5',
        'Programming Language :: Python :: 3.6',
    ],
    keywords='Programming Language, Differential Privacy',
    packages=find_packages(exclude=['tests']),
    install_requires=['ply', 'astunparse', 'z3-solver', 'coloredlogs'],
    extras_require={
        'test': ['pytest-cov', 'pytest', 'coverage', 'jsonpickle'],
    },
    entry_points={
        'console_scripts': [
            'lightdp=lightdp.__main__:main',
        ],
    },
)
