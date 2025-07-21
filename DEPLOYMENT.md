# Guide to deploy on Google Cloud

## Why not Cloud Run?

This here is a guide to help you deploy this Lean server on Google Cloud
(no affiliation to Google, it's just that it's where our server runs). 
Initially, I wanted to use Cloud Run to deploy revisions of the container
in a scalable way, but there are two problems:
- available machines have specs that go up to 16 vCPUs and 64 GB RAM (that's 16 REPLs)
- REPLs require high I/O throughput (SSD or NVMe) and Cloud Run doesn't offer this type of disk

So I ended up deploying on regular VMs, using instance templates and an instance group. 
The instance group manages between min and max instances from an instance template. 
It sits behind a load balancer which acts as the entry point to the API requests. 

## Managed Instance Group

## Instance Group

Create an Instance Group:
- choose stateless managed
- link to an instance template
- min/max as you see fit
- cpu utilization 60% to scale
- init period 60s
- update instance configuration on repair
- port mapping port 80

## Load Balancer

Create a Load Balancer:
- external & regional
- frontend configuration:
    - name
    - protocol http
    - premium ip address
    - port 80
    - keepalive??

## Backend service
- create backend server
    - type instance group
    - http
    - timeout 1200
    - only ipv4
    - create backend
        - new backend select instance group
        - utilization 100%
    - create health check
    - enable logging?
    - security: cloud armor backend security policy
- routing rules: simplest host and path rules

disable external network access to instance template.



The CD pipeline creates an instance template and performs a rolling update of your group. 

