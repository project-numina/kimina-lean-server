from setuptools import find_packages, setup


def parse_requirements(filename):
    with open(filename, "r") as f:
        return [
            line.strip()
            for line in f
            if line and not line.startswith("#") and "--index-url" not in line
        ]


with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setup(
    name="kimina-lean-server",
    version="1.0.1",
    packages=find_packages(),
    install_requires=parse_requirements("requirements.txt"),
    description="",
    long_description=long_description,
    long_description_content_type="text/markdown",
    author="Kimi Team - Project Numina",
    author_email="",
    url="projectnumina.ai",
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
)
