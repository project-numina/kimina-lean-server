-- CreateTable
CREATE TABLE "Repl" (
    "uuid" UUID NOT NULL,
    "created_at" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,
    "max_uses" INTEGER NOT NULL,
    "max_mem" INTEGER NOT NULL,
    "header" TEXT NOT NULL,

    CONSTRAINT "Repl_pkey" PRIMARY KEY ("uuid")
);

-- CreateTable
CREATE TABLE "Proof" (
    "uuid" UUID NOT NULL,
    "id" TEXT NOT NULL,
    "code" TEXT NOT NULL,
    "diagnostics" JSONB,
    "response" JSONB,
    "repl_uuid" UUID NOT NULL,

    CONSTRAINT "Proof_pkey" PRIMARY KEY ("uuid")
);

-- AddForeignKey
ALTER TABLE "Proof" ADD CONSTRAINT "Proof_repl_uuid_fkey" FOREIGN KEY ("repl_uuid") REFERENCES "Repl"("uuid") ON DELETE RESTRICT ON UPDATE CASCADE;
