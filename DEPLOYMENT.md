# Guide to deploy on GCP

Create a Load Balancer:
- external & regional
- frontend configuration:
    - name
    - protocol http
    - premium ip address
    - port 80
    - keepalive??

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


Create an Instance Group:
- choose stateless managed
- link to an instance template
- min/max as you see fit
- cpu utilization 60% to scale
- init period 60s
- update instance configuration on repair
- port mapping port 80

The CD pipeline creates an instance template and performs a rolling update of your group. 

