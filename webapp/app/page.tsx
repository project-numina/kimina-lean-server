'use client'

import { useEffect, useState } from 'react'
import { GoogleOAuthProvider, GoogleLogin } from '@react-oauth/google'
import { Button } from 'shadcn-ui'

interface ApiKey { id: string; key: string }
interface User { id: string; email: string }

export default function Home() {
  const [user, setUser] = useState<User | null>(null)
  const [keys, setKeys] = useState<ApiKey[]>([])

  useEffect(() => {
    if (!user) return
    fetch('/api/keys').then(r => r.json()).then(setKeys)
  }, [user])

  async function handleLogin(cred: any) {
    const resp = await fetch('/api/auth/google', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ credential: cred.credential }),
    })
    if (resp.ok) {
      setUser(await resp.json())
    }
  }

  async function addKey() {
    const resp = await fetch('/api/keys', { method: 'POST' })
    if (resp.ok) setKeys([...keys, await resp.json()])
  }

  async function deleteKey(id: string) {
    await fetch(`/api/keys/${id}`, { method: 'DELETE' })
    setKeys(keys.filter(k => k.id !== id))
  }

  if (!user) {
    return (
      <GoogleOAuthProvider clientId={process.env.NEXT_PUBLIC_GOOGLE_CLIENT_ID!}>
        <div className="flex h-screen items-center justify-center">
          <GoogleLogin onSuccess={handleLogin} />
        </div>
      </GoogleOAuthProvider>
    )
  }

  return (
    <div className="p-8">
      <h1 className="text-xl font-bold mb-4">API Keys</h1>
      <table className="table-auto w-full border">
        <thead>
          <tr>
            <th className="text-left p-2">Key</th>
            <th />
          </tr>
        </thead>
        <tbody>
          {keys.map(k => (
            <tr key={k.id} className="border-t">
              <td className="p-2 font-mono text-sm">{k.key}</td>
              <td className="p-2 text-right">
                <Button variant="destructive" onClick={() => deleteKey(k.id)}>
                  Delete
                </Button>
              </td>
            </tr>
          ))}
        </tbody>
      </table>
      <Button className="mt-4" onClick={addKey}>
        Add Key
      </Button>
    </div>
  )
}
