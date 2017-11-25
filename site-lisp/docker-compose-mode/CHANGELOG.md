# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [1.0.0] - 2017-09-16

### Changed
- Fix namespace of keyword completion function (`docker-compose--keyword-complete-at-point` → `docker-compose-keyword-complete-at-point`)

## [0.3.5] - 2017-09-10

### Changed
- Return no keyword candidates when the version specified in the buffer is invalid
- Improve regular expression to find version
