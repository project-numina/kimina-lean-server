# Kimina Webapp

This is a minimal Next.js + shadcn/ui interface used to manage API keys for the
server. Authentication is performed using Google only.

## Development

```bash
npm install
npm run dev
```

The application expects the environment variable
`NEXT_PUBLIC_GOOGLE_CLIENT_ID` and the server running under the same domain so
API requests can be proxied.
